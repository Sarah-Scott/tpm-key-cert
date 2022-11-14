Require Import Coq.Init.Nat.
Require Import Coq.Sets.Ensembles.

Section CertLAK.

Inductive ak_val : Set :=
| initial : ak_val
| local : ak_val.

Inductive ca_val : Set :=
| tm : ca_val
| oem : ca_val
| owner : ca_val.

Inductive key_val : Set :=
| EK : key_val 
| AK : ak_val -> key_val
| CA : ca_val -> key_val.

Inductive keyType : Type := 
| Private : key_val -> keyType
| Public : key_val -> keyType.

(* TODO: id for tpm and device *)
(* TODO: nonce *)
(* TODO: encrypt *)
Inductive message : Type :=
| key : keyType -> message
| attest : keyType -> message
| sign : message -> keyType -> message
| pair : message -> message -> message.

(* TODO: TPM2_Hash *)
(* TODO: id parameter for MakeCert *)
(* TODO: TPM2_MakeCredential *)
(* TODO: Encrypt and TPM2_ActivateCredential *)
(* TODO: CheckNonce *)
Inductive command : Type :=
| TPM2_Create : key_val -> command
| TPM2_Certify : keyType -> keyType -> command
| MakeCSR : message -> message -> keyType -> command
| TPM2_Sign : message -> keyType -> command
| CheckSig : message -> keyType -> command
| MakeCert : keyType -> keyType -> command
| Sequence : command -> command -> command.

Definition state := Ensemble message.

Notation "m1 , m2" := (pair m1 m2)  (at level 90, left associativity).
Notation "c1 ; c2" := (Sequence c1 c2) (at level 90, left associativity).
Notation "A : x" := (Add message A x) (at level 90, left associativity).

Inductive execute : state -> command -> state -> Prop :=
| E_Create : forall st v, 
    execute st (TPM2_Create v) (st : (key (Private v)) : (key (Public v)))
| E_Certify : forall st k k0,
    In _ st (key k) ->
    In _ st (key k0) ->
    execute st (TPM2_Certify k k0) (st : (sign (attest k) k0))
| E_MakeCSR : forall st m1 m2 k,
    In _ st m1 ->
    In _ st m2 ->
    In _ st (key k) ->
    execute st (MakeCSR m1 m2 k) (st : m1 : m2 : (key k) : (m1, m2, (key k)))
| E_Sign : forall st m k,
    In _ st m -> (* ? *)
    In _ st (key k) ->
    execute st (TPM2_Sign m k) (st : (sign m k))
| E_CheckSigAK : forall st m a,
    In _ st m ->
    In _ st (key (Public (AK a))) ->
    execute st (CheckSig (sign m (Private (AK a))) (Public (AK a))) st
| E_CheckSigCA : forall st m c,
    In _ st m ->
    In _ st (key (Public (CA c))) ->
    execute st (CheckSig (sign m (Private (CA c))) (Public (CA c))) st
| E_MakeCert : forall st k k0,
    In _ st (key k) ->
    In _ st (key k0) ->
    execute st (MakeCert k k0) (st : (sign (key k) k0))
| E_Sequence : forall st st' st'' c1 c2,
    execute st c1 st' ->
    execute st' c2 st'' ->
    execute st (Sequence c1 c2) st''.

Fixpoint send (m : message) : state :=
match m with
  | sign m0 k => (send m0) : (sign m0 k)
  | pair m1 m2 => (Union _ (send m1) (send m2)) : (m1, m2)
  | _ => Singleton _ m
end.

Definition ownerIni : state :=
(*0*)(Singleton _ (key (Private (AK initial)))) :
     (sign (key (Public (AK initial))) (Private (CA oem))).

Definition ownerProtocol : command :=
(*1*)TPM2_Create (AK local) ;
(*2*)TPM2_Certify (Private (AK local)) (Private (AK initial)) ;
(*3*)MakeCSR (sign (key (Public (AK initial))) (Private (CA oem))) 
             (sign (attest (Private (AK local))) (Private (AK initial))) 
             (Public (AK local)) ;
(*4*)TPM2_Sign ((sign (key (Public (AK initial))) (Private (CA oem))), 
                (sign (attest (Private (AK local))) (Private (AK initial))),
                (key (Public (AK local)))) 
               (Private (AK local)).


Definition csrLAK : message :=
  ((sign (key (Public (AK initial))) (Private (CA oem))),
   (sign (attest (Private (AK local))) (Private (AK initial))),
   (key (Public (AK local)))).

Definition ownerFinal : state :=
(*0*)(Singleton _ (key (Private (AK initial)))) :
     (sign (key (Public (AK initial))) (Private (CA oem))) :
(*1*)(key (Private (AK local))) :
     (key (Public (AK local))) :
(*2*)(sign (attest (Private (AK local))) (Private (AK initial))) :
(*3*)(sign (key (Public (AK initial))) (Private (CA oem))) :
     (sign (attest (Private (AK local))) (Private (AK initial))) :
     (key (Public (AK local))) :
     csrLAK :
(*4*)(sign csrLAK (Private (AK local))).
  

Hint Unfold In ownerIni ownerProtocol csrLAK ownerFinal: core.
Hint Resolve Union_introl Union_intror In_singleton Extensionality_Ensembles: core.
Hint Constructors execute : core.

(* auto/eauto not working *)
Theorem ownerCertLAK_spec :
execute ownerIni ownerProtocol ownerFinal.
Proof.
  unfold ownerIni; unfold ownerProtocol; unfold ownerFinal; unfold csrLAK; simpl. 
  repeat eapply E_Sequence. 
  - apply E_Create.
  - apply E_Certify. 
  -- apply Union_introl. apply Union_intror. apply In_singleton.
  -- apply Union_introl. apply Union_introl. apply Union_introl. apply In_singleton.
  - apply E_MakeCSR.
  -- apply Union_introl. apply Union_introl. apply Union_introl. apply Union_intror.
     apply In_singleton.
  -- apply Union_intror. apply In_singleton.
  -- apply Union_introl. apply Union_intror. apply In_singleton.
  - apply E_Sign.
  -- apply Union_intror. apply In_singleton.
  -- apply Union_introl. apply Union_introl. apply Union_introl. apply Union_introl.
     apply Union_introl. apply Union_introl. apply Union_intror. apply In_singleton.
Qed. 

(*5*)(* send 4 *)

Definition caIni : state :=
(*0*)(Singleton _ (key (Private (CA owner)))) :
     (key (Public (CA oem))).

Definition caProtocol : command :=
(*6*)(CheckSig (sign csrLAK (Private (AK local)))
               (Public (AK local))) ;
     (CheckSig (sign (key (Public (AK initial))) (Private (CA oem)))
               (Public (CA oem))) ;
     (CheckSig (sign (attest (Private (AK local))) (Private (AK initial)))
               (Public (AK initial))) ;
(*7*)(MakeCert (Public (AK local)) (Private (CA owner))).

Definition caFinal : state :=
(*0*)(Union _ ((Singleton _ (key (Private (CA owner)))) :
               (key (Public (CA oem))))
(*5*)(send (sign csrLAK (Private (AK local))))) :
(*7*)(sign (key (Public (AK local))) (Private (CA owner))). 

Theorem CertLAK_spec :
execute ownerIni ownerProtocol ownerFinal /\
In _ ownerFinal (sign csrLAK (Private (AK local))) /\
execute (Union _ caIni (send (sign csrLAK (Private (AK local))))) caProtocol caFinal.
Proof.
  repeat try split.
  - apply ownerCertLAK_spec.
  - unfold ownerFinal; unfold csrLAK. apply Union_intror. apply In_singleton.
  - unfold caIni; unfold caProtocol; unfold caFinal; unfold csrLAK; simpl. 
    repeat eapply E_Sequence.
  -- apply E_CheckSigAK.
  --- apply Union_intror. apply Union_introl. apply Union_intror. apply In_singleton.
  --- apply Union_intror. apply Union_introl. apply Union_introl. apply Union_intror.
      apply In_singleton.
  -- apply E_CheckSigCA.
  --- apply Union_intror. apply Union_introl. apply Union_introl. apply Union_introl.
      apply Union_introl. apply Union_introl. apply Union_introl. apply In_singleton.
  --- apply Union_introl. apply Union_intror. apply In_singleton.
  -- apply E_CheckSigAK.
  --- apply Union_intror. apply Union_introl. apply Union_introl. apply Union_introl.
      apply Union_introl. apply Union_intror. apply Union_introl. apply In_singleton.
  --- apply Union_intror. apply Union_introl. apply Union_introl. apply Union_introl.
      apply Union_introl. apply Union_introl. apply Union_introl. apply In_singleton.
  -- apply E_MakeCert.
  --- apply Union_intror. apply Union_introl. apply Union_introl. apply Union_intror.
      apply In_singleton.
  --- apply Union_introl. apply Union_introl. apply In_singleton.
Qed.

End CertLAK.