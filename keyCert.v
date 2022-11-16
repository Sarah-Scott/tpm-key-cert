Require Import Coq.Init.Nat.
Require Import Coq.Sets.Ensembles.





(* Definitions *)
(* *********** *)

(* TODO: TPM and Device identities/info *)
(* TODO: Restricted attribute for keys - TPM state vs Device state *)

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

(* TODO: find better model for random numbers *)
Definition randType := nat.

(* TODO: hash : message -> message *)
Inductive message : Type :=
| key : keyType -> message
| rand : randType -> message
| TPM2_Attest : keyType -> message
| sign : message -> keyType -> message
| credential : message -> randType -> message
| encrypt : message -> keyType -> message
| pair : message -> message -> message.

(* TODO: CheckNonce *)
(* TODO: TPM2_Hash : message -> command *)
Inductive command : Type :=
| TPM2_Create : key_val -> command
| TPM2_Certify : keyType -> keyType -> command
| MakeCSR : message -> message -> keyType -> command
| TPM2_Sign : message -> keyType -> command
| CheckSig : message -> keyType -> command
| TPM2_GetRandom : randType -> command (* TODO: remove randType parameter *)
| TPM2_MakeCredential : keyType -> randType -> keyType -> command
| TPM2_ActivateCredential : message -> keyType -> command
| MakeCert : keyType -> keyType -> command
| Sequence : command -> command -> command.

(* corresponds to what an entity knows *)
Definition state := Ensemble message. (* ? should be a decidable structure ? *)

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
    In _ st (sign m (Private (AK a))) ->
    In _ st (key (Public (AK a))) ->
    execute st (CheckSig (sign m (Private (AK a))) (Public (AK a))) st
| E_CheckSigCA : forall st m c,
    In _ st (sign m (Private (CA c))) -> (* ? required ? *)
    In _ st (key (Public (CA c))) ->
    execute st (CheckSig (sign m (Private (CA c))) (Public (CA c))) st
| E_GetRandom : forall st r,
    execute st (TPM2_GetRandom r) (st : (rand r))
| E_MakeCredential : forall st k r k0,
    In _ st (key k) ->  (* TODO: replace with name *)
    In _ st (rand r) ->
    In _ st (key k0) ->
    execute st (TPM2_MakeCredential k r k0) (st : (encrypt (credential (key k) r) k0))
| E_ActivateCredential : forall st m r,
    In _ st (encrypt (credential m r) (Public EK)) ->
    In _ st (key (Private EK)) ->
    execute st (TPM2_ActivateCredential (encrypt (credential m r) (Public EK)) (Private EK)) (st : (credential m r) : (rand r))
| E_MakeCert : forall st k k0,
    In _ st (key k) ->
    In _ st (key k0) ->
    execute st (MakeCert k k0) (st : (sign (key k) k0))
| E_Sequence : forall st st' st'' c1 c2,
    execute st c1 st' ->
    execute st' c2 st'' ->
    execute st (Sequence c1 c2) st''.





(* Discovery *)
(* ********* *)

(* an entity who knows a message can discover additional messages from it *)
Inductive discoverable : message -> state -> Prop :=
| D_key : forall k,
    discoverable (key k) (Singleton _ (key k))
| D_rand : forall r,
    discoverable (rand r) (Singleton _ (rand r))
| D_Attest : forall k,
    discoverable (TPM2_Attest k) (Singleton _ (TPM2_Attest k))
| D_sign : forall m k st, 
    discoverable m st ->
    discoverable (sign m k) (st : (sign m k))
| D_credential : forall m r st,
    discoverable m st ->
    discoverable (credential m r) (st : (credential m r) : (rand r))
| D_encrypt : forall m k,
    discoverable (encrypt m k) (Singleton _ (encrypt m k))
| D_pair : forall m1 m2 st1 st2,
    discoverable m1 st1 ->
    discoverable m2 st2 ->
    discoverable (pair m1 m2) ((Union _ st1 st2) : (m1, m2)).

(* when sending a message the recipient can discover these additional messages *)
Fixpoint send (m : message) : state :=
match m with
  | sign m0 k => (send m0) : (sign m0 k)
  | credential m0 r => (send m0) : (credential m0 r) : (rand r)
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
(* ********************************************************** *)

(* Numerical comment tags correspond to respective steps in latex documentation *)

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

(* TODO: automate the following proofs *)
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

(*5*)(* send (sign lakCSR (Private (AK local))) *)

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
(* ******************************************************* *)

(* Numerical comment tags correspond to respective steps in latex documentation *)

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

(*4*)(* send (sign iakCSR (Private (AK initial))) *)

Definition caOemIni : state :=
(*0*)(Singleton _ (key (Private (CA oem)))) :
     (key (Public (CA tm))).

Definition r : randType := 5.

Definition caOemSteps1 : command :=
(*5*)(CheckSig (sign iakCSR (Private (AK initial)))
               (Public (AK initial))) ;
     (CheckSig (sign (key (Public EK)) (Private (CA tm)))
               (Public (CA tm))) ;
(*6*)TPM2_GetRandom r ;    
     TPM2_MakeCredential (Public (AK initial)) r (Public EK).

Definition caOemMid : state :=
(*0*)(Union _ caOemIni
(*5*)(send (sign iakCSR (Private (AK initial))))) :
(*6*)(rand r) :
     (encrypt (credential (key (Public (AK initial))) r) (Public EK)).

Theorem correct_caOemMid :
execute oemIni oemSteps1 oemMid /\
In _ oemMid (sign iakCSR (Private (AK initial))) /\
execute (Union _ caOemIni (send (sign iakCSR (Private (AK initial))))) caOemSteps1 caOemMid.
Proof.
  repeat try split.
  - apply correct_oemMid.
  - unfold oemMid. apply Union_intror. apply In_singleton.
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
  -- apply E_GetRandom.
  -- apply E_MakeCredential.
  --- apply Union_introl. apply Union_intror. apply Union_introl. apply Union_introl.
      apply Union_intror. apply In_singleton.
  --- apply Union_intror. apply In_singleton.
  --- apply Union_introl. apply Union_intror. apply Union_introl. apply Union_introl.
      apply Union_introl. apply Union_introl. apply Union_introl. apply Union_introl.
      apply In_singleton.
Qed.

(*7*)(* send (encrypt (credential (key (Public (AK initial))) r) (Public EK)) *)

Definition oemSteps2 : command :=
(*8*)TPM2_ActivateCredential (encrypt (credential (key (Public (AK initial))) r) (Public EK))
                             (Private EK).

Definition oemFinal : state :=
(* *)(Union _ oemMid
(*7*)(send (encrypt (credential (key (Public (AK initial))) r) (Public EK)))) :
(*8*)(credential (key (Public (AK initial))) r) :
     (rand r).

Theorem correct_oemFinal :
execute oemIni oemSteps1 oemMid /\
In _ oemMid (sign iakCSR (Private (AK initial))) /\
execute (Union _ caOemIni (send (sign iakCSR (Private (AK initial))))) caOemSteps1 caOemMid /\
In _ caOemMid (encrypt (credential (key (Public (AK initial))) r) (Public EK)) /\
execute (Union _ oemMid (send (encrypt (credential (key (Public (AK initial))) r) (Public EK)))) oemSteps2 oemFinal.
repeat try split.
- apply correct_caOemMid.
- apply correct_caOemMid.
- apply correct_caOemMid.
- unfold caOemMid. apply Union_intror. apply In_singleton.
- unfold oemFinal; unfold oemMid; unfold oemIni; unfold oemSteps2; unfold iakCSR; simpl.
  apply E_ActivateCredential.
-- apply Union_intror. apply In_singleton.
-- apply Union_introl. apply Union_introl. apply Union_introl. apply Union_introl.
   apply Union_introl. apply Union_introl. apply In_singleton.
Qed.

(* TODO: final OEM CA step *)
