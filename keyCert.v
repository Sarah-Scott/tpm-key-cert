Require Import Coq.Init.Nat.
Require Import Coq.Sets.Ensembles.





Inductive ak_val : Set :=
| initial : ak_val
| local : ak_val.

Inductive ca_val : Set :=
| tm : ca_val   (* tpm manufacturer *)
| oem : ca_val  (* original equipment manufacturer *)
| owner : ca_val.

Inductive key_val : Set :=
| EK : key_val              (* endorsement key *)
| AK : ak_val -> key_val    (* attestation key *)
| CA : ca_val -> key_val.   (* certificate authority key *)

Inductive keyType : Type := 
| Private : key_val -> keyType
| Public : key_val -> keyType.

(* TODO: nonce/secret *)
(* TODO: id for tpm and device *)

(* TODO: id : id_val -> message *)
(* TODO: hash : message -> message *)
(* TODO: credential : message -> secret -> message *)
Inductive message : Type :=
| key : keyType -> message
| TPM2_Attest : keyType -> message
| sign : message -> keyType -> message
| credential : message -> message
| encrypt : message -> keyType -> message
| pair : message -> message -> message.

(* TODO: MakeCert : keyType -> id*)
(* TODO: TPM2_Hash : message -> command *)
(* TODO: MakeCert : keyType -> id -> keyType -> command *)
(* TODO: TPM2_MakeCredential : name -> secret -> keyType -> command *)
(* TODO: CheckNonce *)
Inductive command : Type :=
| TPM2_Create : key_val -> command
| TPM2_Certify : keyType -> keyType -> command
| MakeCSR : message -> message -> keyType -> command
| TPM2_Sign : message -> keyType -> command
| CheckSig : message -> keyType -> command
| TPM2_MakeCredential : keyType -> keyType -> command
| TPM2_ActivateCredential : message -> keyType -> command
| MakeCert : keyType -> keyType -> command
| Sequence : command -> command -> command.

Definition state := Ensemble message. (* ? should be decidable ? *)

Notation "m1 , m2" := (pair m1 m2)  (at level 90, left associativity).
Notation "c1 ; c2" := (Sequence c1 c2) (at level 90, left associativity).
Notation "A : x" := (Add message A x) (at level 90, left associativity).

Inductive execute : state -> command -> state -> Prop :=
| E_Create : forall st v, 
    execute st (TPM2_Create v) (st : (key (Private v)) : (key (Public v)))
| E_Certify : forall st k k0,
    In _ st (key k) ->
    In _ st (key k0) ->
    execute st (TPM2_Certify k k0) (st : (sign (TPM2_Attest k) k0))
| E_MakeCSR : forall st m1 m2 k,
    In _ st m1 ->
    In _ st m2 ->
    In _ st (key k) ->
    execute st (MakeCSR m1 m2 k) (st : (m1, m2, (key k)))
| E_Sign : forall st m k,
    In _ st m ->
    In _ st (key k) ->
    execute st (TPM2_Sign m k) (st : (sign m k))
| E_CheckSigAK : forall st m a,
    In _ st (sign m (Private (AK a))) -> (* ? required ? *)
    In _ st (key (Public (AK a))) ->
    execute st (CheckSig (sign m (Private (AK a))) (Public (AK a))) st
| E_CheckSigCA : forall st m c,
    In _ st (sign m (Private (CA c))) -> (* ? required ? *)
    In _ st (key (Public (CA c))) ->
    execute st (CheckSig (sign m (Private (CA c))) (Public (CA c))) st
| E_MakeCredential : forall st k k0, (* TODO: add secret credential *)
    In _ st (key k) ->  (* TODO: replace with name *)
    In _ st (key k0) ->
    execute st (TPM2_MakeCredential k k0) (st : (encrypt (credential (key k)) k0))
| E_ActivateCredential : forall st m,
    In _ st (encrypt (credential m) (Private EK)) ->
    In _ st (key (Public EK)) ->
    (* TODO: add secret to state *)
    execute st (TPM2_ActivateCredential (encrypt (credential m) (Private EK)) (Public EK)) (st : (credential m))
| E_MakeCert : forall st k k0,
    In _ st (key k) ->
    In _ st (key k0) ->
    execute st (MakeCert k k0) (st : (sign (key k) k0))
| E_Sequence : forall st st' st'' c1 c2,
    execute st c1 st' ->
    execute st' c2 st'' ->
    execute st (Sequence c1 c2) st''.







Inductive discoverable : message -> state -> Prop :=
| D_key : forall k,
    discoverable (key k) (Singleton _ (key k))
| D_Attest : forall k,
    discoverable (TPM2_Attest k) (Singleton _ (TPM2_Attest k))
| D_sign : forall m k st, 
    discoverable m st ->
    discoverable (sign m k) (st : (sign m k))
| D_credential : forall m st,
    discoverable m st ->
    discoverable (credential m) (st : (credential m))
| D_encrypt : forall m k,
    discoverable (encrypt m k) (Singleton _ (encrypt m k))
| D_pair : forall m1 m2 st1 st2,
    discoverable m1 st1 ->
    discoverable m2 st2 ->
    discoverable (pair m1 m2) ((Union _ st1 st2) : (m1, m2)).
    
(* when sending a message the recipient can discover everything in this result *)
Fixpoint send (m : message) : state :=
match m with
  | sign m0 k => (send m0) : (sign m0 k)
  | credential m0 => (send m0) : (credential m0)
  | pair m1 m2 => (Union _ (send m1) (send m2)) : (m1, m2)
  | _ => Singleton _ m
end.
    
Theorem discoverableSend : forall m st,
discoverable m st ->
send m = st.
Proof.
  intros m st H; induction H; simpl; subst; reflexivity.
Qed.

Lemma sendDiscoverable' : forall m,
discoverable m (send m).
Proof.
  intros m; induction m; simpl; constructor; assumption.
Qed.

Theorem sendDiscoverable : forall m st,
send m = st -> 
discoverable m st.
Proof.
  intros m st H; induction m; subst; apply sendDiscoverable'.
Qed.

Theorem iff_DiscoverableSend : forall m st,
discoverable m st <-> send m = st.
Proof.
  split.
  - apply discoverableSend.
  - apply sendDiscoverable.
Qed.








(* Owner creation of LAK certificate based on IAK certificate *)

Definition ownerIni : state :=
(*0*)(Singleton _ (key (Private (AK initial)))) :
     (sign (key (Public (AK initial))) (Private (CA oem))).

Definition lakCSR : message :=
((sign (key (Public (AK initial))) (Private (CA oem))),
 (sign (TPM2_Attest (Private (AK local))) (Private (AK initial))),
 (key (Public (AK local)))).

Definition ownerSteps : command :=
(*1*)TPM2_Create (AK local) ;
(*2*)TPM2_Certify (Private (AK local)) (Private (AK initial)) ;
(*3*)MakeCSR (sign (key (Public (AK initial))) (Private (CA oem))) 
             (sign (TPM2_Attest (Private (AK local))) (Private (AK initial))) 
             (Public (AK local)) ;
(*4*)TPM2_Sign lakCSR (Private (AK local)).

Definition ownerFinal : state :=
(*0*)ownerIni :
(*1*)(key (Private (AK local))) :
     (key (Public (AK local))) :
(*2*)(sign (TPM2_Attest (Private (AK local))) (Private (AK initial))) :
(*3*)lakCSR :
(*4*)(sign lakCSR (Private (AK local))).

(*
Hint Unfold In ownerIni ownerSteps lakCSR ownerFinal: core.
Hint Resolve Union_introl Union_intror In_singleton Extensionality_Ensembles: core.
Hint Constructors execute : core.
*)

Theorem correct_ownerFinal :
execute ownerIni ownerSteps ownerFinal.
Proof.
  unfold ownerFinal; unfold ownerIni; unfold ownerSteps; unfold lakCSR; simpl. 
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
  -- apply Union_introl. apply Union_introl. apply Union_introl. apply Union_intror.
     apply In_singleton.
Qed.

(*5*)(* send 4 *)

Definition caOwnerIni : state :=
(*0*)(Singleton _ (key (Private (CA owner)))) :
     (key (Public (CA oem))).

Definition caOwnerSteps : command :=
(*6*)(CheckSig (sign lakCSR (Private (AK local)))
               (Public (AK local))) ;
     (CheckSig (sign (key (Public (AK initial))) (Private (CA oem)))
               (Public (CA oem))) ;
     (CheckSig (sign (TPM2_Attest (Private (AK local))) (Private (AK initial)))
               (Public (AK initial))) ;
(*7*)(MakeCert (Public (AK local)) (Private (CA owner))).

Definition caOwnerFinal : state :=
(*0*)(Union _ caOwnerIni
(*5*)(send (sign lakCSR (Private (AK local))))) :
(*7*)(sign (key (Public (AK local))) (Private (CA owner))). 

Theorem CertLAK_spec :
execute ownerIni ownerSteps ownerFinal /\
In _ ownerFinal (sign lakCSR (Private (AK local))) /\
execute (Union _ caOwnerIni (send (sign lakCSR (Private (AK local))))) caOwnerSteps caOwnerFinal.
Proof.
  repeat try split.
  - apply correct_ownerFinal.
  - unfold ownerFinal; unfold ownerIni; unfold lakCSR. apply Union_intror. apply In_singleton.
  - unfold caOwnerFinal; unfold caOwnerIni; unfold caOwnerSteps; unfold lakCSR; simpl. 
    repeat eapply E_Sequence.
  -- apply E_CheckSigAK.
  --- apply Union_intror. apply Union_intror. apply In_singleton.
  --- apply Union_intror. apply Union_introl. apply Union_introl. apply Union_intror.
      apply In_singleton.
  -- apply E_CheckSigCA.
  --- apply Union_intror. apply Union_introl. apply Union_introl. apply Union_introl.
      apply Union_introl. apply Union_introl. apply Union_intror. apply In_singleton.
  --- apply Union_introl. apply Union_intror. apply In_singleton.
  -- apply E_CheckSigAK.
  --- apply Union_intror. apply Union_introl. apply Union_introl. apply Union_introl.
      apply Union_introl. apply Union_intror. apply Union_intror. apply In_singleton.
  --- apply Union_intror. apply Union_introl. apply Union_introl. apply Union_introl.
      apply Union_introl. apply Union_introl. apply Union_introl. apply In_singleton.
  -- apply E_MakeCert.
  --- apply Union_intror. apply Union_introl. apply Union_introl. apply Union_intror.
      apply In_singleton.
  --- apply Union_introl. apply Union_introl. apply In_singleton.
Qed.











(* OEM creation of IAK certificate based on EK certificate *)

Definition oemIni : state :=
(*0*)(Singleton _ (key (Private EK))) :
     (sign (key (Public EK)) (Private (CA tm))).

Definition iakCSR : message :=
((sign (key (Public EK)) (Private (CA tm))),
 (key (Public (AK initial))),
 (key (Public (AK initial)))).

Definition oemSteps1 : command :=
(*1*)TPM2_Create (AK initial) ;
(*2*)MakeCSR (sign (key (Public EK)) (Private (CA tm)))
             (key (Public (AK initial))) (* TODO: replace with id*)
             (Public (AK initial)) ;
(*3*)TPM2_Sign iakCSR (Private (AK initial)).

Definition oemMid : state :=
(*0*)oemIni :
(*1*)(key (Private (AK initial))) :
     (key (Public (AK initial))) :
(*2*)iakCSR :
(*3*)(sign iakCSR (Private (AK initial))).


Theorem correct_oemMid :
execute oemIni oemSteps1 oemMid.
Proof.
  unfold oemMid; unfold oemIni; unfold oemSteps1; unfold iakCSR; simpl. 
  repeat eapply E_Sequence. 
  - apply E_Create.
  - apply E_MakeCSR.
  -- apply Union_introl. apply Union_introl. apply Union_intror. apply In_singleton.
  -- apply Union_intror. apply In_singleton.
  -- apply Union_intror. apply In_singleton.
  - apply E_Sign.
  -- apply Union_intror. apply In_singleton.
  -- apply Union_introl. apply Union_introl. apply Union_intror. apply In_singleton.
Qed.

(*4*)(* send 3 *)

Definition caOemIni : state :=
(*0*)(Singleton _ (key (Private (CA oem)))) :
     (key (Public (CA tm))).

Definition caOemSteps1 : command :=
(*5*)(CheckSig (sign iakCSR (Private (AK initial)))
               (Public (AK initial))) ;
     (CheckSig (sign (key (Public EK)) (Private (CA tm)))
               (Public (CA tm))) ;
(*6*)TPM2_MakeCredential (Public (AK initial)) (Public EK).

Definition caOemMid : state :=
(*0*)(Union _ caOemIni
(*5*)(send (sign iakCSR (Private (AK initial))))) :
(*6*)(encrypt (credential (key (Public (AK initial)))) (Public EK)).

Theorem correct_caOemMid :
execute oemIni oemSteps1 oemMid /\
In _ oemMid (sign iakCSR (Private (AK initial))) /\
execute (Union _ caOemIni (send (sign iakCSR (Private (AK initial))))) caOemSteps1 caOemMid.
Proof.
  repeat try split.
  - apply correct_oemMid.
  - unfold oemMid; unfold iakCSR. apply Union_intror. apply In_singleton.
  - unfold caOemMid; unfold caOemIni; unfold caOemSteps1; unfold iakCSR; simpl. 
    repeat eapply E_Sequence.
  -- apply E_CheckSigAK.
  --- apply Union_intror. apply Union_intror. apply In_singleton.
  --- apply Union_intror. apply Union_introl. apply Union_introl. apply Union_intror.
      apply In_singleton.
  -- apply E_CheckSigCA.
  --- apply Union_intror. apply Union_introl. apply Union_introl. apply Union_introl.
      apply Union_introl. apply Union_introl. apply Union_intror. apply In_singleton.
  --- apply Union_introl. apply Union_intror. apply In_singleton.
  -- apply E_MakeCredential.
  --- apply Union_intror. apply Union_introl. apply Union_introl. apply Union_intror.
      apply In_singleton.
  --- apply Union_intror. apply Union_introl. apply Union_introl. apply Union_introl.
      apply Union_introl. apply Union_introl. apply Union_introl. apply In_singleton.
Qed.

(*7*)(* send 6*)

Definition oemSteps2 : command :=
(*8*)TPM2_ActivateCredential (encrypt (credential (key (Public (AK initial)))) (Public EK))
                             (Private EK).

Definition oemFinal : state :=
(* *)(Union _ oemMid
(*7*)(send (encrypt (credential (key (Public (AK initial)))) (Public EK)))) :
(*8*)(credential (key (Public (AK initial)))).













(* Owner creation of LAK certificate based on IAK certificate *)
Section CertLAK.

Inductive ak_val : Set :=
| initial : ak_val
| local : ak_val.

Inductive ca_val : Set :=
| tm : ca_val   (* tpm manufacturer *)
| oem : ca_val  (* original equipment manufacturer *)
| owner : ca_val.

Inductive key_val : Set :=
| EK : key_val              (* endorsement key *)
| AK : ak_val -> key_val    (* attestation key *)
| CA : ca_val -> key_val.   (* certificate authority key *)

Inductive keyType : Type := 
| Private : key_val -> keyType
| Public : key_val -> keyType.

(* TODO: id for tpm and device *)
(* TODO: nonce *)
(* TODO: encrypt *)
Inductive message : Type :=
| key : keyType -> message
| TPM2_Attest : keyType -> message
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

Definition state := Ensemble message. (* ? should be decidable ? *)

Notation "m1 , m2" := (pair m1 m2)  (at level 90, left associativity).
Notation "c1 ; c2" := (Sequence c1 c2) (at level 90, left associativity).
Notation "A : x" := (Add message A x) (at level 90, left associativity).

Inductive execute : state -> command -> state -> Prop :=
| E_Create : forall st v, 
    execute st (TPM2_Create v) (st : (key (Private v)) : (key (Public v)))
| E_Certify : forall st k k0,
    In _ st (key k) ->
    In _ st (key k0) ->
    execute st (TPM2_Certify k k0) (st : (sign (TPM2_Attest k) k0))
| E_MakeCSR : forall st m1 m2 k,
    In _ st m1 ->
    In _ st m2 ->
    In _ st (key k) ->
    execute st (MakeCSR m1 m2 k) (st : m1 : m2 : (key k) : (m1, m2, (key k)))
| E_Sign : forall st m k,
    In _ st m ->
    In _ st (key k) ->
    execute st (TPM2_Sign m k) (st : (sign m k))
| E_CheckSigAK : forall st m a,
    In _ st m -> (* ? required ? *)
    In _ st (key (Public (AK a))) ->
    execute st (CheckSig (sign m (Private (AK a))) (Public (AK a))) st
| E_CheckSigCA : forall st m c,
    In _ st m -> (* ? required ? *)
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

Inductive discoverable : message -> state -> Prop :=
| D_key : forall k,
    discoverable (key k) (Singleton _ (key k))
| D_Attest : forall k,
    discoverable (TPM2_Attest k) (Singleton _ (TPM2_Attest k))
| D_sign : forall m k st, 
    discoverable m st ->
    discoverable (sign m k) (st : (sign m k))
| D_pair : forall m1 m2 st1 st2,
    discoverable m1 st1 ->
    discoverable m2 st2 ->
    discoverable (pair m1 m2) ((Union _ st1 st2) : (m1, m2)).

(* when sending a message the recipient can discover everything in this result *)
Fixpoint send (m : message) : state :=
match m with
  | sign m0 k => (send m0) : (sign m0 k)
  | pair m1 m2 => (Union _ (send m1) (send m2)) : (m1, m2)
  | _ => Singleton _ m
end.

Theorem discoverableSend : forall m st,
discoverable m st ->
send m = st.
Proof.
  intros m st H; induction H; simpl; subst; reflexivity.
Qed.

Lemma sendDiscoverable' : forall m,
discoverable m (send m).
Proof.
  intros m; induction m; simpl; constructor; assumption.
Qed.

Theorem sendDiscoverable : forall m st,
send m = st -> 
discoverable m st.
Proof.
  intros m st H; induction m; subst; apply sendDiscoverable'.
Qed.

Theorem iff_DiscoverableSend : forall m st,
discoverable m st <-> send m = st.
Proof.
  split.
  - apply discoverableSend.
  - apply sendDiscoverable.
Qed.

Definition ownerIni : state :=
(*0*)(Singleton _ (key (Private (AK initial)))) :
     (sign (key (Public (AK initial))) (Private (CA oem))).

Definition ownerProtocol : command :=
(*1*)TPM2_Create (AK local) ;
(*2*)TPM2_Certify (Private (AK local)) (Private (AK initial)) ;
(*3*)MakeCSR (sign (key (Public (AK initial))) (Private (CA oem))) 
             (sign (TPM2_Attest (Private (AK local))) (Private (AK initial))) 
             (Public (AK local)) ;
(*4*)TPM2_Sign ((sign (key (Public (AK initial))) (Private (CA oem))), 
                (sign (TPM2_Attest (Private (AK local))) (Private (AK initial))),
                (key (Public (AK local)))) 
               (Private (AK local)).


Definition csrLAK : message :=
  ((sign (key (Public (AK initial))) (Private (CA oem))),
   (sign (TPM2_Attest (Private (AK local))) (Private (AK initial))),
   (key (Public (AK local)))).

Definition ownerFinal : state :=
(*0*)(Singleton _ (key (Private (AK initial)))) :
     (sign (key (Public (AK initial))) (Private (CA oem))) :
(*1*)(key (Private (AK local))) :
     (key (Public (AK local))) :
(*2*)(sign (TPM2_Attest (Private (AK local))) (Private (AK initial))) :
(*3*)(sign (key (Public (AK initial))) (Private (CA oem))) :
     (sign (TPM2_Attest (Private (AK local))) (Private (AK initial))) :
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
     (CheckSig (sign (TPM2_Attest (Private (AK local))) (Private (AK initial)))
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