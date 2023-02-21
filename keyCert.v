
  Require Import Coq.Init.Nat.
  Require Import Coq.Lists.List.
  Import ListNotations.





(* TPM Keys *)
(* ******** *)


(* Each key pair has a unique identifier *)
  Definition key_id := nat.


(* Attributes relevant to this specification *)

  Inductive restrict_att : Type :=
  | Restricted
  | NonRestricted.

  Inductive sign_att : Type :=
  | Signing
  | NonSigning.

  Inductive decrypt_att : Type :=
  | Decrypting
  | NonDecrypting.


(* Key pair definitions *)

  Inductive pubKey : Type :=
  | Public : key_id -> restrict_att -> sign_att -> decrypt_att -> pubKey.

  Inductive privKey : Type :=
  | Private : key_id -> restrict_att -> sign_att -> decrypt_att -> privKey.


(* Functions to get a key's inverse *)

  Definition pubtoPrivKey (k : pubKey) : privKey :=
    match k with
    | Public i r s d => Private i r s d
    end.

  Definition privToPubKey (k : privKey) : pubKey :=
    match k with
    | Private i r s d => Public i r s d
    end.


(* Attribute requirements for EK, AK, DevID, and CA keys *)

  Definition endorsementKey (k : pubKey) : Prop :=
    match k with
    | Public _ Restricted NonSigning Decrypting => True
    | _ => False
    end.

  Definition attestationKey (k : pubKey) : Prop :=
    match k with
    | Public _ Restricted Signing NonDecrypting => True
    | _ => False
    end.

  Definition devidKey (k : pubKey) : Prop :=
    match k with
    | Public _ NonRestricted Signing NonDecrypting => True
    | _ => False
    end.

  Definition caKey (k : pubKey) : Prop :=
    match k with
    | Public _ NonRestricted Signing _ => True
    | _ => False
    end.

(* Roles in this specification *)
(* Currently unused. Should include adversary? *)
  Inductive entity : Set :=
  | tm
  | oem
  | owner.



(* Commands *)
(* ******** *)


(* Arbitrary type to model random numbers *)
  Definition randType := nat.

(* Messages includes all structures required in this specification *)
  Inductive message : Type :=
  | publicKey : pubKey -> message
  | privateKey : privKey -> message
  | rand : randType -> message
  | hash : message -> message
  | sign : message -> privKey -> message
  | TPM2B_Attest : pubKey -> message
  | credential : message -> randType -> message
  | encrypt : message -> pubKey -> message
  | TCG_CSR_IDevID : message -> pubKey -> message
  | TCG_CSR_LDevID : message -> message -> message
  | certificate : pubKey -> message    (* TODO: pubKey -> id -> message *)
  | pair : message -> message -> message.


(* Includes both TPM and non-TPM commands required in this specification *)
  Inductive command : Type :=
  | CheckAttributes : pubKey -> restrict_att -> sign_att -> decrypt_att -> command
  | TPM2_GetRandom : randType -> command
  | CheckNonce : message -> randType -> command
  | TPM2_Hash : message -> command
  | CheckHash : message -> message -> command
  | TPM2_Sign : message -> privKey -> command
  | CheckSig : message -> pubKey -> command
  | TPM2_Certify : pubKey -> privKey -> command
  | TPM2_MakeCredential : message -> randType -> pubKey -> command
  | TPM2_ActivateCredential : message -> privKey -> privKey -> command
  | MakeCSR_IDevID : message -> pubKey -> command
  | MakeCSR_LDevID : message -> message -> command
  | MakeCert : pubKey -> privKey -> command  (* TODO: pubKey -> id -> privKey -> message *)
  | CheckCert : message -> pubKey -> command
  | Sequence : command -> command -> command.


(* State corresponds to what an entity knows *)
(* Not necessarily exhaustive *)
  Definition state := list message.


(* TPM State contains everything produced by a TPM command *)
(* Subset of the general state *)
  Definition tpm_state := list message.


(* Notations for pairs of messages and sequences of commands *)
  Notation "m1 ,, m2" := (pair m1 m2)  (at level 90, left associativity).
  Notation "c1 ;; c2" := (Sequence c1 c2) (at level 90, left associativity).





(* Execution of Commands *)
(* ********************* *)


(* Inductive proposition describing command execution *)
  Inductive execute : tpm_state * state -> command -> tpm_state * state -> Prop :=
(*
  CheckAttributes
  ***************
  Inputs: 
    Public Key
    Attributes
  Success Conditions:
    Public Key has all Attributes
  Updates to State:
    None
*)
  | E_CheckAttributes : forall stTPM st i r s d,
      execute (stTPM, st)
              (CheckAttributes (Public i r s d) r s d)
              (stTPM,
               st)
(*
  TPM2_GetRandom
  **************
  Inputs: 
    Random Number
  Success Conditions:
    None
  Updates to State:
    Random Number to TPM State
*)
  | E_GetRandom : forall stTPM st g,
      execute 
        (stTPM, st)
        (TPM2_GetRandom g)
        (rand g :: stTPM,
         rand g :: st)
(*
  CheckNonce
  **********
  Inputs: 
    Random Number
    Golden Value
  Success Conditions:
    Golden Value resides in TPM
    Random Number is Golden Value
  Updates to State:
    None
*)
  | E_CheckNonce : forall stTPM st g,
      In (rand g) stTPM ->
      execute (stTPM, st)
              (CheckNonce (rand g) g)
              (stTPM,
               st)
(*
  TPM2_Hash
  *********
  Inputs: 
    Message
  Success Conditions:
    None
  Updates to State:
    The hash of Message to TPM State
*)
  | E_Hash : forall stTPM st m,
      In m st ->
      execute (stTPM, st)
              (TPM2_Hash m)
              (hash m :: stTPM,
               hash m :: st)
(*
  CheckHash
  *********
  Inputs: 
    Hash
    Message
  Success Conditions:
    Hash is in state
    Message is in state
    Hash is the hash of Message
  Updates to State:
    None
*)
  | E_CheckHash : forall stTPM st m,
      In (hash m) st ->
      In m st ->
      execute (stTPM, st)
              (CheckHash (hash m) m)
              (stTPM,
               st)
(*
  TPM2_Sign
  *********
  Inputs: 
    Message
    Private Key
  Success Conditions:
    Private Key resides in TPM
    Message resides in TPM
    Private Key has Restricted and Signing attributes
  Updates to State:
    Message signed by Private Key to TPM State
*)
  | E_SignR : forall stTPM st m i d,
      In (privateKey (Private i Restricted Signing d)) stTPM ->
      In m stTPM ->
      execute (stTPM,st)
              (TPM2_Sign m (Private i Restricted Signing d))
              (sign m (Private i Restricted Signing d) :: stTPM,
               sign m (Private i Restricted Signing d) :: st)
(*
  TPM2_Sign
  *********
  Inputs: 
    Message
    Private Key
  Success Conditions:
    Private Key resides in TPM
    Message is in state
    Private Key has NonRestricted and Signing attributes
  Updates to State:
    Message signed by Private Key to TPM State
*)
  | E_SignNR : forall stTPM st m i d,
      In (privateKey (Private i NonRestricted Signing d)) stTPM ->
      In m st ->
      execute (stTPM, st)
              (TPM2_Sign m (Private i NonRestricted Signing d))
              (sign m (Private i NonRestricted Signing d) :: stTPM,
               sign m (Private i NonRestricted Signing d) :: st)
(*
  CheckSig
  ********
  Inputs: 
    Signature
    Public Key
  Success Conditions:
    Signature is in state
    Public Key is in state
    Public Key is the inverse of the key that created Signature
  Updates to State:
    None
*)
  | E_CheckSig : forall stTPM st m i r s d,
      In (sign m (Private i r s d)) st ->
      In (publicKey (Public i r s d)) st ->
      execute (stTPM, st)
              (CheckSig (sign m (Private i r s d)) (Public i r s d))
              (stTPM,
               st)
(*
  TPM2_Certify
  ************
  Inputs: 
    Public Key
    Private Key
  Success Conditions:
    The inverse of Public Key resides in TPM
    Private Key resides in TPM
    Private Key has Signing attribute
  Updates to State:
    TPM2B_Attest structure of Public Key signed by Private Key to TPM State
*)
  | E_Certify : forall stTPM st i r s d i0 r0 d0,
      In (privateKey (Private i r s d)) stTPM -> 
      In (privateKey (Private i0 r0 Signing d0)) stTPM ->
      execute (stTPM, st)
              (TPM2_Certify (Public i r s d) (Private i0 r0 Signing d0))
              (sign (TPM2B_Attest (Public i r s d)) (Private i0 r0 Signing d0) :: stTPM,
               sign (TPM2B_Attest (Public i r s d)) (Private i0 r0 Signing d0) :: st)
(*
  TPM2_MakeCredential
  *******************
  Inputs: 
    Message
    Random Number
    Public Key
  Success Conditions:
    Message in in state
    Random Number resides in TPM
    Public Key has Decrypting attribute
  Updates to State:
    Credential structure of Message and Random Number encrypted with Public Key to TPM State
*)
  | E_MakeCredential : forall stTPM st m g i r s,
      In m st ->
      In (rand g) stTPM ->
      In (publicKey (Public i r s Decrypting)) st ->
      execute (stTPM, st)
              (TPM2_MakeCredential m g (Public i r s Decrypting)) 
              (encrypt (credential m g) (Public i r s Decrypting) :: stTPM,
               encrypt (credential m g) (Public i r s Decrypting) :: st)
(*
  TPM2_ActivateCredential
  ***********************
  Inputs: 
    Encrypted Credential (Credential contains Message and Random Number)
    Private Key A
    Private Key B
  Success Conditions:
    Encrypted Credential is in state
    Private Key A resides in TPM
    Private Key B resides in TPM
    Private Key A is the inverse of the key that created Encrypted Credential
    Message is the hash of the inverse of Private Key B
  Updates to State:
    Random Number and Credential to TPM State
*)
  | E_ActivateCredential : forall stTPM st m g i r s d i0 r0 s0 d0,
      In (encrypt (credential m g) (Public i r s d)) st ->
      In (privateKey (Private i r s d)) stTPM ->
      In (privateKey (Private i0 r0 s0 d0)) stTPM ->
      execute (stTPM, m::st) (CheckHash m (publicKey (Public i0 r0 s0 d0))) (stTPM, m::st) ->
      execute (stTPM, st)
              (TPM2_ActivateCredential (encrypt (credential m g) (Public i r s d)) 
                                      (Private i r s d)
                                      (Private i0 r0 s0 d0)) 
              (rand g :: credential m g :: stTPM,
               rand g :: credential m g :: st)
(*
  MakeCSR_IDevID
  **************
  Inputs: 
    Message
    Public Key
  Success Conditions:
    Message is in state
    Public Key is in state
  Updates to State:
    TCG_CSR_IDevID of Message and Public Key to State
*)
  | E_MakeCSR_IDevID : forall stTPM st m i r s d,
      In m st ->
      In (publicKey (Public i r s d)) st ->
      execute (stTPM, st)
              (MakeCSR_IDevID m (Public i r s d))
              (stTPM,
               TCG_CSR_IDevID m (Public i r s d) :: st)
(*
  MakeCSR_LDevID
  **************
  Inputs: 
    Message A
    Message B
  Success Conditions:
    Message A is in state
    Message B is in state
  Updates to State:
    TCG_CSR_LDevID of Message A and Message B to State
*)
  | E_MakeCSR_LDevID : forall stTPM st m1 m2,
      In m1 st ->
      In m2 st ->
      execute (stTPM, st)
              (MakeCSR_LDevID m1 m2)
              (stTPM,
               TCG_CSR_LDevID m1 m2 :: st)
(*
  MakeCert
  ********
  Inputs: 
    Public Key
    Private Key
  Success Conditions:
    Public Key is in state
    Private Key resides in TPM
    Private Key has NonRestricted and Signing attributes
  Updates to State:
    Certificate of Public Key signed by Private Key to TPM State
*)
  | E_MakeCert : forall stTPM st i r s d i0 d0,
      In (publicKey (Public i r s d)) st ->
      In (privateKey (Private i0 NonRestricted Signing d0)) stTPM ->
      execute (stTPM, st)
              (MakeCert (Public i r s d) (Private i0 NonRestricted Signing d0))
              (sign (certificate (Public i r s d)) (Private i0 NonRestricted Signing d0) :: stTPM,
               sign (certificate (Public i r s d)) (Private i0 NonRestricted Signing d0) :: st)
(*
  CheckCert
  *********
  Inputs: 
    Signature
    Public Key
  Success Conditions:
    Signature is in state
    Public Key is in state
    Signature contains Certificate
    Public Key is the inverse of the key that created Signature
  Updates to State:
    None
*)
  | E_CheckCert : forall stTPM st k i r s d,
      In (sign (certificate k) (Private i r s d)) st ->
      In (publicKey (Public i r s d)) st ->
      execute (stTPM, st)
              (CheckCert (sign (certificate k) (Private i r s d)) (Public i r s d))
              (stTPM,
              st)
(*
  Sequence
  ********
  Inputs: 
    Command A
    Command B
  Success Conditions:
    None
  Updates to State:
    Effects from Command A and Command B
*)
  | E_Sequence : forall ini mid fin c1 c2,
      execute ini c1 mid ->
      execute mid c2 fin ->
      execute ini (Sequence c1 c2) fin.


(* Execute relation is a partial function *)
  Theorem execute_deterministic : forall ini c fin1 fin2,
    execute ini c fin1 ->
    execute ini c fin2 ->
    fin1 = fin2.
  Proof.
    intros ini c fin1 fin2 E1 E2.
    generalize dependent fin2.
    induction E1; intros fin2 E2; inversion E2; subst; try reflexivity.
    assert (mid = mid0) as EQ_mid.
    - apply IHE1_1; assumption.
    - apply IHE1_2; rewrite EQ_mid; assumption.
  Qed.


  Ltac execute_constructor :=
    match goal with
    | [ |- execute _ (Sequence _ _) _ ] => eapply E_Sequence
    | [ |- execute _ _ _] => constructor
    end.


  Lemma sequence_split : forall ini c1 c2 fin,
    execute ini (c1 ;; c2) fin ->
    exists mid, (execute ini c1 mid /\ execute mid c2 fin).
  Proof.
    intros ini c1 c2 fin H; inversion H; subst.
    exists mid; split; assumption.
  Qed.




(* Message Discovery *)
(* ***************** *)

(* An entity who knows a message can discover additional messages from it *)
  Inductive discoverable : message -> state -> Prop :=
  | D_publicKey : forall k,
      discoverable (publicKey k) [publicKey k]
  | D_privateKey : forall k,
      discoverable (privateKey k) [privateKey k]
  | D_rand : forall r,
      discoverable (rand r) [rand r]
  | D_hash : forall m,
      discoverable (hash m) [hash m]
  | D_sign : forall m k st,               (* contents of signature *)
      discoverable m st ->
      discoverable (sign m k) ((sign m k)::st)
  | D_Attest : forall k,                  (* contents of TPM2_Attest structure *)
      discoverable (TPM2B_Attest k) [(TPM2B_Attest k); (publicKey k)] 
  | D_credential : forall m r,
      discoverable (credential m r) [credential m r]
  | D_encrypt : forall m k,
      discoverable (encrypt m k) [encrypt m k]
  | D_CSR_IDevID : forall m k st,         (* contents of TCG_CSR_IDevID *)
      discoverable m st ->
      discoverable (TCG_CSR_IDevID m k) ([(TCG_CSR_IDevID m k); (publicKey k)]++st)
  | D_CSR_LDevID : forall m1 m2 st1 st2,  (* contents of TCG_CSR_LDevID *)
      discoverable m1 st1 ->
      discoverable m2 st2 ->
      discoverable (TCG_CSR_LDevID m1 m2) ((TCG_CSR_LDevID m1 m2)::st1++st2)
  | D_certificate : forall k,             (* contents of certificate *)
      discoverable (certificate k) [(certificate k); (publicKey k)]
  | D_pair : forall m1 m2 st1 st2,        (* contents of pair *)
      discoverable m1 st1 ->
      discoverable m2 st2 -> 
      discoverable (pair m1 m2) ((m1,,m2)::(st1++st2)).


(* When sending a message the recipient can discover these additional messages *)
  Fixpoint send (m : message) : state :=
  match m with
    | sign m0 k => ((sign m0 k)::(send m0))
    | TPM2B_Attest k => [(TPM2B_Attest k); (publicKey k)]
    | TCG_CSR_IDevID m0 k => ([(TCG_CSR_IDevID m0 k); publicKey k]++(send m0))
    | TCG_CSR_LDevID m1 m2 => ((TCG_CSR_LDevID m1 m2)::(send m1)++(send m2))
    | certificate k => [(certificate k); (publicKey k)]
    | pair m1 m2 => ((m1,,m2)::((send m1)++(send m2)))
    | _ => [m]
  end.



(* Discoverable relation and Send function are equivalent *)

  Lemma discoverableSend : forall m st,
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

  Lemma sendDiscoverable : forall m st,
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















(* OEM creation of IAK certificate based on EK certificate *)
(* ******************************************************* *)

(* Numerical comment tags correspond to respective steps in latex documentation *)

Module Type IAK_Cert_Protocol.

(* OEM parameters *)
  Parameter pubNewKey : pubKey.
  Parameter privNewKey : privKey.
  Parameter pubEK : pubKey.
  Parameter privEK : privKey.
  Parameter certEK : message.

(* CA parameters *)
  Parameter pubCA : pubKey.
  Parameter privCA : privKey.
  Parameter pubTM : pubKey.
  Parameter r : randType.


(* All keys must be distinct *)
  Axiom DistinctKeys :
    pubNewKey <> pubEK /\
    pubNewKey <> pubCA /\
    pubNewKey <> pubTM /\
    pubEK <> pubCA /\
    pubEK <> pubTM /\
    pubCA <> pubTM.


  Definition iniTPM : tpm_state :=
  [ publicKey pubNewKey ;
    privateKey privNewKey ;
    publicKey pubEK ;
    privateKey privEK ].

  Definition ini : state :=
  [ publicKey pubNewKey ;
    privateKey privNewKey ;
    certEK ;    (* EK certificate *)
    publicKey pubEK ;
    privateKey privEK ].


  Definition c1 : command :=
  MakeCSR_IDevID certEK pubNewKey ;;                              (* 1 *)
  TPM2_Hash (TCG_CSR_IDevID certEK pubNewKey) ;;                  (* 2 *)
  TPM2_Sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey.  (* 3 *)


  Definition midTPM : state :=
  sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey ::
  hash (TCG_CSR_IDevID certEK pubNewKey) ::
  iniTPM.

  Definition mid : state :=
  sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey ::
  hash (TCG_CSR_IDevID certEK pubNewKey) ::
  (TCG_CSR_IDevID certEK pubNewKey) ::
  ini.

(*
  send ((TCG_CSR_IDevID certEK pubNewKey),, (sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey))   (* 4 *)
*)


  Definition iniTPM_CA : tpm_state :=
  [ privateKey privCA ;
    publicKey pubCA ].

  Definition ini_CA : state :=
  [ publicKey pubTM ;
    privateKey privCA ;
    publicKey pubCA ].


  Definition c1_CA : command :=
  CheckHash (hash (TCG_CSR_IDevID certEK pubNewKey)) (TCG_CSR_IDevID certEK pubNewKey) ;; (* 5a *)
  CheckSig (sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey) pubNewKey ;;        (* 5b *)
  CheckCert certEK pubTM ;;                                                               (* 5c *)
  CheckAttributes pubNewKey Restricted Signing NonDecrypting ;;                           (* 5d *)
  TPM2_Hash (publicKey pubNewKey) ;;                                                      (* 6 *)
  TPM2_GetRandom r ;;                                                                     (* 7 *)
  TPM2_MakeCredential (hash (publicKey pubNewKey)) r pubEK.                               (* 8 *)


  Definition midTPM_CA : tpm_state :=
  encrypt (credential (hash (publicKey pubNewKey)) r) pubEK ::
  rand r ::
  hash (publicKey pubNewKey) ::
  iniTPM_CA.

  Definition mid_CA : state :=
  encrypt (credential (hash (publicKey pubNewKey)) r) pubEK ::
  rand r ::
  hash (publicKey pubNewKey) ::
  send ((TCG_CSR_IDevID certEK pubNewKey),, (sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey)) ++
  ini_CA.

(*
  send (encrypt (credential (hash (publicKey pubNewKey)) r) pubEK)    (* 9 *)
*)

  Definition c2 : command :=
  TPM2_ActivateCredential (encrypt (credential (hash (publicKey pubNewKey)) r) pubEK) privEK (privNewKey).  (* 10 *)


  Definition finTPM : tpm_state :=
  rand r ::
  credential (hash (publicKey pubNewKey)) r ::
  midTPM.

  Definition fin : state :=
  rand r ::
  credential (hash (publicKey pubNewKey)) r  ::
  send (encrypt (credential (hash (publicKey pubNewKey)) r) pubEK) ++
  mid.

(*
  send (rand r)    (* 11 *)
*)

  Definition c2_CA : command :=
  CheckNonce (rand r) r ;;    (* 12 *)
  MakeCert pubNewKey privCA.  (* 13 *)

  Definition finTPM_CA : state := 
  sign (certificate pubNewKey) privCA ::
  midTPM_CA.

  Definition fin_CA : state := 
  sign (certificate pubNewKey) privCA ::
  send (rand r) ++
  mid_CA.


(* Protocol specification *)
Axiom CertIAK_spec :
  execute (iniTPM, ini) c1 (midTPM, mid) /\     (* Steps 0 - 3 *)
  In (TCG_CSR_IDevID certEK pubNewKey) mid /\   (* Step 4 *)
  In (sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey) mid /\  (* Step 4 *)
  execute (iniTPM_CA, send ((TCG_CSR_IDevID certEK pubNewKey),, sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey) ++ ini_CA)
           c1_CA                                (* Steps 5 - 8*)
          (midTPM_CA, mid_CA) /\ 
  In (encrypt (credential (hash (publicKey pubNewKey)) r) pubEK) mid_CA /\  (* Step 9 *)
  execute (midTPM, send (encrypt (credential (hash (publicKey pubNewKey)) r) pubEK) ++ mid) 
           c2                                   (* Step 10 *)
          (finTPM, fin) /\
  In (rand r) fin /\  (* Step 11 *)
  execute (midTPM_CA, send (rand r) ++ mid_CA)
           c2_CA                                (* Step 12 - 13 *)
          (finTPM_CA, fin_CA).




(* Protocol Assurances *)
(* ******************* *)


(* A TPM is authentic *)
(* EK Certificate is valid *)
  Theorem authenticTPM : exists st st',
    execute st (CheckCert certEK pubTM) st'.
  Proof.
    assert (H : execute (iniTPM_CA, send ((TCG_CSR_IDevID certEK pubNewKey),, sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey) ++ ini_CA) c1_CA (midTPM_CA, mid_CA)). apply CertIAK_spec.
    repeat (apply sequence_split in H; destruct H; destruct H).
    eexists; eexists; apply H4.
  Qed.


(* This specific TPM is authentic and is represented by the EK Certificate *)
(* EK resident in this TPM corresponds to the EK Certificate *)
  Theorem authenticThisTPM : 
    certEK = sign (certificate pubEK) (pubtoPrivKey pubTM).
  Proof.
(* 
  Since the CA executed "CheckCert cerEK pubTM", 
  we know that "certEK" must be in the form "sign (certificate k) pubTM" for some "k : pubKey". 
*)
    assert (H_CheckCert : exists st st', execute st (CheckCert certEK pubTM) st'). apply authenticTPM.
    destruct H_CheckCert as [ini H_CheckCert]. destruct H_CheckCert as [fin H_CheckCert].
    inversion H_CheckCert. subst. simpl. 
    assert (H_certEK : sign (certificate k) (Private i r0 s d) = certEK). assumption. clear H H0 H2 H4.
(* 
  Since the CA executed "TPM2_MakeCredential (hash (publicKey pubNewKey)) r pubEK)", 
  we know that "pubEK" must have the "Decrypting" attribute
  and "pubEK" must be in the CA's state.
*)
    assert (H : execute (iniTPM_CA, send ((TCG_CSR_IDevID certEK pubNewKey),, sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey) ++ ini_CA) c1_CA (midTPM_CA, mid_CA)). apply CertIAK_spec.
    repeat (apply sequence_split in H; destruct H; destruct H).
    inversion H0. subst.
(*
  Since "pubEK" must be in the CA's state,
  we can show that "pubEK" must be discoverable from the sent "certEK"
  and hence "k" is "pubEK".
*)
    rewrite <- H_certEK in H16. unfold ini_CA in H16. simpl in H16.
    destruct H16 as [H16|H16]. inversion H16.
    destruct H16 as [H16|H16]. inversion H16.
    destruct H16 as [H16|H16]. inversion H16.
    destruct H16 as [H16|H16]. inversion H16.
    destruct H16 as [H16|H16]. inversion H3. subst. rewrite <- H9 in H16. inversion H16.
    destruct H16 as [H16|H16]. inversion H16.
    destruct H16 as [H16|H16]. inversion H16.
    destruct H16 as [H16|H16]. inversion H16. reflexivity.
    destruct H16 as [H16|H16]. inversion H16.
    destruct H16 as [H16|H16]. inversion H16.
    destruct H16 as [H16|H16]. inversion H16. rewrite H8 in H7. symmetry in H7. apply DistinctKeys in H7. inversion H7.
    destruct H16 as [H16|H16]. inversion H16.
    destruct H16 as [H16|H16]. inversion H16. rewrite H8 in H7. symmetry in H7. apply DistinctKeys in H7. inversion H7.
    inversion H16.
  Qed.




(* This AK is authentic *)
(* AK in CSR is resident in the same TPM as the EK *)
  Theorem authenticThisAK :
    In (privateKey privNewKey) finTPM /\
    In (privateKey privEK) finTPM.
  Proof.
    unfold finTPM; unfold midTPM; unfold iniTPM;
    split; simpl; auto 9.
  Qed.


End IAK_Cert_Protocol.















Module myIAK <: IAK_Cert_Protocol.

  Definition pubNewKey : pubKey := Public 11 Restricted Signing NonDecrypting.
  Definition privNewKey : privKey := Private 11 Restricted Signing NonDecrypting.
  Definition pubEK : pubKey := Public 10 Restricted NonSigning Decrypting.
  Definition privEK : privKey := Private 10 Restricted NonSigning Decrypting.
  Definition certEK : message := sign (certificate (Public 10 Restricted NonSigning Decrypting)) 
                                      (Private 0 NonRestricted Signing NonDecrypting).

  Definition pubCA : pubKey := Public 1 NonRestricted Signing NonDecrypting.
  Definition privCA : privKey := Private 1 NonRestricted Signing NonDecrypting.
  Definition pubTM : pubKey := Public 0 NonRestricted Signing NonDecrypting.
  Definition r : randType := 5.


  Theorem DistinctKeys :
    pubNewKey <> pubEK /\
    pubNewKey <> pubCA /\
    pubNewKey <> pubTM /\
    pubEK <> pubCA /\
    pubEK <> pubTM /\
    pubCA <> pubTM.
  Proof.
    repeat split; intros H; inversion H.
  Qed.


  Definition iniTPM : tpm_state :=
  [ publicKey pubNewKey ;
  privateKey privNewKey ;
  publicKey pubEK ;
  privateKey privEK ].

  Definition ini : state :=
  [ publicKey pubNewKey ;
  privateKey privNewKey ;
  certEK ;    (* EK certificate *)
  publicKey pubEK ;
  privateKey privEK ].


  Definition c1 : command :=
  MakeCSR_IDevID certEK pubNewKey ;;                              (* 1 *)
  TPM2_Hash (TCG_CSR_IDevID certEK pubNewKey) ;;                  (* 2 *)
  TPM2_Sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey.  (* 3 *)


  Definition midTPM : state :=
  sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey ::
  hash (TCG_CSR_IDevID certEK pubNewKey) ::
  iniTPM.

  Definition mid : state :=
  sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey ::
  hash (TCG_CSR_IDevID certEK pubNewKey) ::
  (TCG_CSR_IDevID certEK pubNewKey) ::
  ini.

  Local Hint Unfold mid midTPM c1 ini iniTPM : core.


  (*
  send ((TCG_CSR_IDevID certEK pubNewKey),, (sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey))   (* 4 *)
  *)


  Definition iniTPM_CA : tpm_state :=
  [ privateKey privCA ;
  publicKey pubCA ].

  Definition ini_CA : state :=
  [ publicKey pubTM ;
  privateKey privCA ;
  publicKey pubCA ].


  Definition c1_CA : command :=
  CheckHash (hash (TCG_CSR_IDevID certEK pubNewKey)) (TCG_CSR_IDevID certEK pubNewKey) ;; (* 5a *)
  CheckSig (sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey) pubNewKey ;;        (* 5b *)
  CheckCert certEK pubTM ;;                                                               (* 5c *)
  CheckAttributes pubNewKey Restricted Signing NonDecrypting ;;                           (* 5d *)
  TPM2_Hash (publicKey pubNewKey) ;;                                                      (* 6 *)
  TPM2_GetRandom r ;;                                                                     (* 7 *)
  TPM2_MakeCredential (hash (publicKey pubNewKey)) r pubEK.                               (* 8 *)


  Definition midTPM_CA : tpm_state :=
  encrypt (credential (hash (publicKey pubNewKey)) r) pubEK ::
  rand r ::
  hash (publicKey pubNewKey) ::
  iniTPM_CA.

  Definition mid_CA : state :=
  encrypt (credential (hash (publicKey pubNewKey)) r) pubEK ::
  rand r ::
  hash (publicKey pubNewKey) ::
  send ((TCG_CSR_IDevID certEK pubNewKey),, (sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey)) ++
  ini_CA.

  Local Hint Unfold mid_CA midTPM_CA c1_CA ini_CA iniTPM_CA : core.

  (*
  send (encrypt (credential (hash (publicKey pubNewKey)) r) pubEK)    (* 9 *)
  *)

  Definition c2 : command :=
  TPM2_ActivateCredential (encrypt (credential (hash (publicKey pubNewKey)) r) pubEK) privEK (privNewKey).  (* 10 *)


  Definition finTPM : tpm_state :=
  rand r ::
  credential (hash (publicKey pubNewKey)) r ::
  midTPM.

  Definition fin : state :=
  rand r ::
  credential (hash (publicKey pubNewKey)) r  ::
  send (encrypt (credential (hash (publicKey pubNewKey)) r) pubEK) ++
  mid.

  Local Hint Unfold fin finTPM c2 : core.

  (*
  send (rand r)    (* 11 *)
  *)

  Definition c2_CA : command :=
  CheckNonce (rand r) r ;;    (* 12 *)
  MakeCert pubNewKey privCA.  (* 13 *)

  Definition finTPM_CA : state := 
  sign (certificate pubNewKey) privCA ::
  midTPM_CA.

  Definition fin_CA : state := 
  sign (certificate pubNewKey) privCA ::
  send (rand r) ++
  mid_CA.

  Local Hint Unfold fin_CA finTPM_CA c2_CA : core.

  (* Protocol specification *)
  Theorem CertIAK_spec :
    execute (iniTPM, ini) c1 (midTPM, mid) /\     (* Steps 0 - 3 *)
    In (TCG_CSR_IDevID certEK pubNewKey) mid /\   (* Step 4 *)
    In (sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey) mid /\  (* Step 4 *)
    execute (iniTPM_CA, send ((TCG_CSR_IDevID certEK pubNewKey),, sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey) ++ ini_CA)
           c1_CA                                (* Steps 5 - 8*)
          (midTPM_CA, mid_CA) /\ 
    In (encrypt (credential (hash (publicKey pubNewKey)) r) pubEK) mid_CA /\  (* Step 9 *)
    execute (midTPM, send (encrypt (credential (hash (publicKey pubNewKey)) r) pubEK) ++ mid) 
           c2                                   (* Step 10 *)
          (finTPM, fin) /\
    In (rand r) fin /\  (* Step 11 *)
    execute (midTPM_CA, send (rand r) ++ mid_CA)
           c2_CA                                (* Step 12 - 13 *)
          (finTPM_CA, fin_CA).
    Proof.
      repeat split; autounfold; repeat execute_constructor; simpl; auto 11.
    Qed.






    (*TODO *)
   (* 
(* Protocol Assurances *)
(* ******************* *)


(* A TPM is authentic *)
(* EK Certificate is valid *)
Theorem authenticTPM : exists st st',
execute st (CheckCert certEK pubTM) st'.
Proof.
assert (H : execute (iniTPM_CA, send ((TCG_CSR_IDevID certEK pubNewKey),, sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey) ++ ini_CA) c1_CA (midTPM_CA, mid_CA)). apply CertIAK_spec.
repeat (apply sequence_split in H; destruct H; destruct H).
eexists; eexists; apply H4.
Qed.


(* This specific TPM is authentic and is represented by the EK Certificate *)
(* EK resident in this TPM corresponds to the EK Certificate *)
Theorem authenticThisTPM : 
certEK = sign (certificate pubEK) (pubtoPrivKey pubTM).
Proof.
(* 
Since the CA executed "CheckCert cerEK pubTM", 
we know that "certEK" must be in the form "sign (certificate k) pubTM" for some "k : pubKey". 
*)
assert (H_CheckCert : exists st st', execute st (CheckCert certEK pubTM) st'). apply authenticTPM.
destruct H_CheckCert as [ini H_CheckCert]. destruct H_CheckCert as [fin H_CheckCert].
inversion H_CheckCert. subst. simpl. 
assert (H_certEK : sign (certificate k) (Private i r0 s d) = certEK). assumption. clear H H0 H2 H4.
(* 
Since the CA executed "TPM2_MakeCredential (hash (publicKey pubNewKey)) r pubEK)", 
we know that "pubEK" must have the "Decrypting" attribute
and "pubEK" must be in the CA's state.
*)
assert (H : execute (iniTPM_CA, send ((TCG_CSR_IDevID certEK pubNewKey),, sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey) ++ ini_CA) c1_CA (midTPM_CA, mid_CA)). apply CertIAK_spec.
repeat (apply sequence_split in H; destruct H; destruct H).
inversion H0. subst.
(*
Since "pubEK" must be in the CA's state,
we can show that "pubEK" must be discoverable from the sent "certEK"
and hence "k" is "pubEK".
*)
rewrite <- H_certEK in H16. unfold ini_CA in H16. simpl in H16.
destruct H16 as [H16|H16]. inversion H16.
destruct H16 as [H16|H16]. inversion H16.
destruct H16 as [H16|H16]. inversion H16.
destruct H16 as [H16|H16]. inversion H16.
destruct H16 as [H16|H16]. inversion H3. subst. rewrite <- H9 in H16. inversion H16.
destruct H16 as [H16|H16]. inversion H16.
destruct H16 as [H16|H16]. inversion H16.
destruct H16 as [H16|H16]. inversion H16. reflexivity.
destruct H16 as [H16|H16]. inversion H16.
destruct H16 as [H16|H16]. inversion H16.
destruct H16 as [H16|H16]. inversion H16. rewrite H8 in H7. symmetry in H7. apply DistinctKeys in H7. inversion H7.
destruct H16 as [H16|H16]. inversion H16.
destruct H16 as [H16|H16]. inversion H16. rewrite H8 in H7. symmetry in H7. apply DistinctKeys in H7. inversion H7.
inversion H16.
Qed.




(* This AK is authentic *)
(* AK in CSR is resident in the same TPM as the EK *)
Theorem authenticThisAK :
In (privateKey privNewKey) finTPM /\
In (privateKey privEK) finTPM.
Proof.
unfold finTPM; unfold midTPM; unfold iniTPM;
split; simpl; auto 9.
Qed.

*)
End myIAK. 

