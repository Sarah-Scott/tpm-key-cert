
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Import ListNotations.




Class DecEq (A : Type) := 
{
  decEq : forall x1 x2 : A, {x1 = x2} + {x1 <> x2}
}.

Ltac fdeq :=
  eauto; intros HC; inversion HC; congruence.

Ltac ddeq :=
  econstructor;
  match goal with
  | |- forall x1 x2 : _,_ =>
      destruct x1, x2; eauto;
      try right; fdeq
  end.

Ltac ideq :=
  econstructor;
  match goal with
  | |- forall x1 x2 : _,_ =>
      induction x1 as [|x1 IHx1]; destruct x2;
      try destruct (IHx1 x2); eauto
  end.








(* TPM Keys *)
(* ******** *)


(* Each key pair has a unique identifier *)
Definition keyIdType := nat.


(* TPM key attributes relevant to this specification *)

Inductive Restricted : Type :=
| Restricting
| NonRestricting.

Inductive Sign : Type :=
| Signing
| NonSigning.

Inductive Decrypt : Type :=
| Decrypting
| NonDecrypting.

Inductive FixedTPM : Type :=
| Fixing
| NonFixing.



(* Key pair definitions *)

Inductive pubKey : Type :=
| Public : keyIdType -> Restricted -> Sign -> Decrypt -> FixedTPM -> pubKey.

Inductive privKey : Type :=
| Private : keyIdType -> Restricted -> Sign -> Decrypt -> FixedTPM -> privKey.


(* Functions to get a key's inverse *)

Definition pubToPrivKey (k : pubKey) : privKey :=
  match k with
  | Public i r s d f => Private i r s d f
  end.

Definition privToPubKey (k : privKey) : pubKey :=
  match k with
  | Private i r s d f => Public i r s d f
  end.


(* Attribute requirements for EK, AK, DevID, and CA keys *)

Definition endorsementKey (k : pubKey) : Prop :=
  match k with
  | Public _ Restricting NonSigning Decrypting Fixing => True
  | _ => False
  end.

Definition attestationKey (k : pubKey) : Prop :=
  match k with
  | Public _ Restricting Signing NonDecrypting Fixing => True
  | _ => False
  end.

Definition devidKey (k : pubKey) : Prop :=
  match k with
  | Public _ NonRestricting Signing NonDecrypting Fixing => True
  | _ => False
  end.

Definition caKey (k : pubKey) : Prop :=
  match k with
  | Public _ NonRestricting Signing NonDecrypting Fixing => True
  | _ => False
  end.



(* Decidable equality of keys *)
Local Instance decEq_keyID : DecEq keyIdType.
  ideq.
Qed.

Local Instance decEq_Restricted : DecEq Restricted.
  ddeq.
Qed.
  
Local Instance decEq_Sign : DecEq Sign.
  ddeq.
Qed.

Local Instance decEq_Decrypt : DecEq Decrypt.
  ddeq.
Qed.

Local Instance decEq_FixedTPM : DecEq FixedTPM.
  ddeq.
Qed.

Local Instance decEq_pubKey : DecEq pubKey.
  econstructor; induction x1; destruct x2;
  destruct (decEq k k0);
  destruct (decEq r r0);
  destruct (decEq s s0);
  destruct (decEq d d0);
  destruct (decEq f f0);
  subst; eauto; right; fdeq.
Qed.

Local Instance decEq_privKey : DecEq privKey.
  econstructor; induction x1; destruct x2.
  destruct (decEq k k0); 
  destruct (decEq r r0);
  destruct (decEq s s0); 
  destruct (decEq d d0);
  destruct (decEq f f0);
  subst; eauto; right; fdeq.
Qed.






















(* Messages *)
(* ******** *)


(* Arbitrary type to model identifying information *)
Definition tpmInfoType := nat.
Definition deviceInfoType := nat.

Inductive identifier : Type :=
| TPM_info : tpmInfoType -> identifier
| Device_info : deviceInfoType -> identifier.


Inductive signedCert : Type :=
| Cert : pubKey -> identifier -> privKey -> signedCert.


(* Arbitrary type to model random numbers *)
Definition randType := nat.


(* Messages includes all structures required in this specification *)
Inductive message : Type :=
| publicKey : pubKey -> message
| privateKey : privKey -> message
| hash : message -> message
| signature : message -> privKey -> message
| TPM2B_Attest : pubKey -> message
| encryptedCredential : message -> randType -> pubKey -> message
| randomNum : randType -> message
| TCG_CSR_IDevID : identifier -> signedCert -> pubKey -> message
| TCG_CSR_LDevID : message -> signedCert -> message
| signedCertificate : signedCert -> message
| pair : message -> message -> message.


(* Decidable equality of messages *)

Local Instance decEq_identifier : DecEq identifier.
  econstructor; induction x1; destruct x2; try (right; fdeq);
  try destruct (decEq t t0);
  try destruct (decEq d d0);
  subst; eauto; right; fdeq.
Qed.

Local Instance decEq_signedCert : DecEq signedCert.
  econstructor; destruct x1, x2;
  destruct (decEq p p1); 
  destruct (decEq i i0); 
  destruct (decEq p0 p2);
  subst; eauto; right; fdeq.
Qed.

Local Instance decEq_randType : DecEq randType.
  ideq.
Qed.

Local Instance decEq_message : DecEq message.
  econstructor; induction x1; destruct x2; try (right; fdeq);
  try destruct (decEq p p0);
  try destruct (decEq r r0);
  try destruct (decEq i i0);
  try destruct (decEq s s0);
  try destruct (IHx1 x2);
  subst; eauto; try (right; fdeq).
  destruct (IHx1_1 x2_1);
  destruct (IHx1_2 x2_2);
  subst; eauto; right; fdeq.
Qed.












(* Commands *)
(* ******** *)


(* Includes both TPM and non-TPM commands required in this specification *)
Inductive command : Type :=
| TPM2_Hash : message -> command
| CheckHash : message -> message -> command
| TPM2_Sign : message -> privKey -> command
| TPM2_Certify : pubKey -> privKey -> command
| CheckSig : message -> pubKey -> command
| TPM2_MakeCredential : message -> randType -> pubKey -> command
| TPM2_ActivateCredential : message -> privKey -> privKey -> command
| MakeCSR_IDevID : identifier -> signedCert -> pubKey -> command
| MakeCSR_LDevID : message -> signedCert -> command
| CheckCert : signedCert -> pubKey -> command
| CheckAttributes : pubKey -> Restricted -> Sign -> Decrypt -> FixedTPM -> command
| MakePair : message -> message -> command.


(* State corresponds to what an entity knows *)
(* States are treated as sets *)

Definition state := list message.

(* TPM State isSuperseqOf everything produced by a TPM command *)
(* Subset of the general state *)
Definition tpm_state := list message.


(* Set inclusion over states *)

Definition Included (st1 st2 : list message) : Prop := forall m,
In m st1 ->
In m st2.

Notation "st1 \subsetOf st2" := (Included st1 st2) (at level 92, left associativity).

Lemma Included_transitive : forall st1 st2 st3,
  st1 \subsetOf st2 ->
  st2 \subsetOf st3 ->
  st1 \subsetOf st3.
Proof.
  intros st1 st2 st3 H12 H23; intros m' I; 
  apply H23; apply H12; assumption.
Qed.




(* Decidable equality of commands *)
Local Instance decEq_command : DecEq command.
  econstructor; induction x1; destruct x2; try (right; fdeq);
  try destruct (decEq p p0);
  try destruct (decEq r r0);
  try destruct (decEq s s0);
  try destruct (decEq d d0);
  try destruct (decEq f f0);
  try destruct (decEq m m0);
  try destruct (decEq i i0);
  try (destruct (decEq m m1); destruct (decEq m0 m2));
  try (destruct (decEq p p1); destruct (decEq p0 p2));
  subst; eauto; right; fdeq.
Qed.







(* Execution of Commands *)
(* ********************* *)


(* Inductive proposition describing individual command execution *)
(* Relates an initial state, a command, and a final state *)
  Inductive execute : tpm_state * state -> command -> tpm_state * state -> Prop :=
(*
  TPM2_Hash
  *********
  Inputs: 
    Message
  Success Conditions:
    Message is in state
  Updates to State:
    hash of Message to TPM State
*)
| E_Hash : forall stTPM st m,
    In m st ->
    execute (stTPM, st)
            (TPM2_Hash m)
            (hash m :: stTPM, hash m :: st)
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
            (stTPM, st)
(*
  TPM2_Sign Restricted
  ********************
  Inputs: 
    Message
    Private Key
  Success Conditions:
    Private Key resides in TPM
    Message resides in TPM
    Private Key has Restricting and Signing attributes
  Updates to State:
    Message signed by Private Key
*)
| E_SignR : forall stTPM st m i d f,
    In (privateKey (Private i Restricting Signing d f)) stTPM ->
    In m stTPM ->
    execute (stTPM,st)
            (TPM2_Sign m (Private i Restricting Signing d f))
            (stTPM, signature m (Private i Restricting Signing d f) :: st)
(*
  TPM2_Sign Not-Restricted
  ************************
  Inputs: 
    Message
    Private Key
  Success Conditions:
    Private Key resides in TPM
    Message is in state
    Private Key has NonRestricting and Signing attributes
  Updates to State:
    Message signed by Private Key
*)
| E_SignNR : forall stTPM st m i d f,
    In (privateKey (Private i NonRestricting Signing d f)) stTPM ->
    In m st ->
    execute (stTPM, st)
            (TPM2_Sign m (Private i NonRestricting Signing d f))
            (stTPM, signature m (Private i NonRestricting Signing d f) :: st)
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
    TPM2B_Attest structure of Public Key signed by Private Key
*)
| E_Certify : forall stTPM st i r s d f i0 r0 d0 f0,
    In (privateKey (Private i r s d f)) stTPM -> 
    In (privateKey (Private i0 r0 Signing d0 f0)) stTPM ->
    execute (stTPM, st)
            (TPM2_Certify (Public i r s d f) (Private i0 r0 Signing d0 f0))
            (stTPM, signature (TPM2B_Attest (Public i r s d f)) (Private i0 r0 Signing d0 f0) :: st)
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
| E_CheckSig : forall stTPM st m i r s d f,
    In (signature m (Private i r s d f)) st ->
    In (publicKey (Public i r s d f)) st ->
    execute (stTPM, st)
            (CheckSig (signature m (Private i r s d f)) (Public i r s d f))
            (stTPM, st)
(*
  TPM2_MakeCredential
  *******************
  Inputs:
    Name
    Random Number
    Public Key
  Success Conditions:
    Name is in state
    Random Number is in state
    Public Key is in state
    Public Key is an endorsement key
  Updates to State:
    credential containing Name and Random Number encrypted by Public Key
*)
| E_MakeCredential : forall stTPM st n g i,
    In n st ->
    In (randomNum g) st ->
    In (publicKey (Public i Restricting NonSigning Decrypting Fixing)) st ->
    execute (stTPM, st)
            (TPM2_MakeCredential n g (Public i Restricting NonSigning Decrypting Fixing))
            (stTPM, encryptedCredential n g (Public i Restricting NonSigning Decrypting Fixing) :: st)
(*
  TPM2_ActivateCredential
  ***********************
  Inputs: 
    Encrypted Credential (isSuperseqOf Name and Random Number)
    Private Key A
    Private Key B
  Success Conditions:
    Encrypted Credential is in state
    Private Key A resides in TPM
    Private Key B resides in TPM
    Private Key A is the inverse of the key that created Encrypted Credential
    Name is the hash of the inverse of Private Key B
  Updates to State:
    Random Number
*)
| E_ActivateCredential : forall stTPM st n g i r s d f i0 r0 s0 d0 f0,
    In (encryptedCredential n g (Public i r s d f)) st ->
    In (privateKey (Private i r s d f)) stTPM ->
    In (privateKey (Private i0 r0 s0 d0 f0)) stTPM ->
    execute (stTPM, n::st) (CheckHash n (publicKey (Public i0 r0 s0 d0 f0))) (stTPM, n::st) ->
    execute (stTPM, st)
            (TPM2_ActivateCredential (encryptedCredential n g (Public i r s d f)) 
                                     (Private i r s d f)
                                     (Private i0 r0 s0 d0 f0)) 
            (stTPM, randomNum g :: st)


(*
  MakeCSR_IDevID
  **************
  Inputs: 
    Identifier
    Certificate
    Public Key
  Success Conditions:
    Certificate is in state
    Public Key is in state
  Updates to State:
    TCG_CSR_IDevID containing Identifier, Certificate, and Public Key
*)
| E_MakeCSR_IDevID : forall stTPM st id crt k,
    In (signedCertificate crt) st ->
    In (publicKey k) st ->
    execute (stTPM, st)
            (MakeCSR_IDevID id crt k)
            (stTPM, TCG_CSR_IDevID id crt k :: st)
(*
  MakeCSR_LDevID
  **************
  Inputs: 
    Message
    Certificate
  Success Conditions:
    Message is in state
    Certificate is in state
  Updates to State:
    TCG_CSR_LDevID containing Message and Certificate
*)
| E_MakeCSR_LDevID : forall stTPM st m crt,
    In m st ->
    In (signedCertificate crt) st ->
    execute (stTPM, st)
            (MakeCSR_LDevID m crt)
            (stTPM, TCG_CSR_LDevID m crt :: st)
(*
  CheckCert
  *********
  Inputs: 
    Signed Certificate
    Public Key
  Success Conditions:
    Signed Certificate is in state
    Public Key is in state
    Public Key is the inverse of the key that created Signed Certificate
  Updates to State:
    None
*)
| E_CheckCert : forall stTPM st k id i r s d f,
    In (signedCertificate (Cert k id (Private i r s d f))) st ->
    In (publicKey (Public i r s d f)) st ->
    execute (stTPM, st)
            (CheckCert (Cert k id (Private i r s d f)) (Public i r s d f))
            (stTPM, st)
(*
  CheckAttributes
  ***************
  Inputs: 
    Public Key
    Attributes
  Success Conditions:
    Public Key is in state
    Public Key has all Attributes
  Updates to State:
    None
*)
| E_CheckAttributes : forall stTPM st i r s d f,
    In (publicKey (Public i r s d f)) st ->
    execute (stTPM, st)
            (CheckAttributes (Public i r s d f) r s d f)
            (stTPM, st)
(*
  MakePair
  ********
  Inputs:
    Message A
    Message B
  Success Conditions:
    Message A is in state
    Message B is in state
  Updates to State:
    pair containing Message A and Message B *)
| E_MakePair : forall stTPM st m1 m2,
    In m1 st ->
    In m2 st ->
    execute (stTPM, st)
            (MakePair m1 m2)
            (stTPM, pair m1 m2 :: st).


Lemma exec_deterministic : forall ini c fin1 fin2,
  execute ini c fin1 ->
  execute ini c fin2 ->
  fin1 = fin2.
Proof.
  intros ini c fin1 fin2 E1 E2;
  destruct E1; inversion E2; subst; reflexivity.
Qed.

Lemma exec_expansion : forall iniTPM ini c finTPM fin,
  execute (iniTPM,ini) c (finTPM,fin) ->
  (iniTPM \subsetOf finTPM) /\
  (ini \subsetOf fin).
Proof.
  intros iniTPM ini c finTPM fin E; split;
  destruct c; inversion E; subst; 
  intros m' I; try (repeat apply in_cons); assumption.
Qed.

Lemma exec_cannotGenerateKey : forall c iniTPM ini finTPM fin k,
  execute (iniTPM, ini) c (finTPM, fin) ->
  In (privateKey k) finTPM ->
  In (privateKey k) iniTPM.
Proof.
  destruct c; intros iniTPM ini finTPM fin k E I;
  inversion E; subst; try inversion I as [EQ_false | I']; 
  try inversion EQ_false; assumption.
Qed.

Lemma exec_cannotGenerateRand_contrapositive : forall c iniTPM ini finTPM fin g,
  execute (iniTPM, ini) c (finTPM, fin) ->
  ~ In (randomNum g) ini ->
  (forall n k, ~ In (encryptedCredential n g k) ini) ->
  ~ In (randomNum g) fin.
Proof.
  induction c; intros iniTPM ini finTPM fin g E Ng N;
  inversion E; subst; try assumption;
  intros HC; inversion HC; try inversion H; subst; try congruence;
  destruct (N n (Public i r s d f)); assumption.
Qed.


Lemma exec_cannotGenerateCred_contrapositive : forall c iniTPM ini finTPM fin n g k,
  execute (iniTPM, ini) c (finTPM, fin) ->
  ~ In (encryptedCredential n g k) ini ->
  ~ In (randomNum g) ini ->
  ~ In (encryptedCredential n g k) fin.
Proof.
  induction c;  intros iniTPM ini finTPM fin n g k E Ne N;
  inversion E; subst; try assumption;
  intros HC; inversion HC; try inversion H; congruence.
Qed.













(* Execution of Sequences of Commands *)
(* ********************************** *)


Inductive sequence : Type :=
| Sequence : command -> sequence -> sequence
| Done : sequence.

Infix ";;" := Sequence (at level 60, right associativity).

Fixpoint command_in_sequence (cmd : command) (seq : sequence)  :=
  match seq with
  | c ;; s =>
      if (decEq cmd c)
      then True
      else command_in_sequence cmd s
  | Done => False
  end.

Inductive seq_execute : tpm_state * state -> sequence -> tpm_state * state -> Prop :=
| SE_Seq : forall ini mid fin c s,
    execute ini c mid ->
    seq_execute mid s fin ->
    seq_execute ini (Sequence c s) fin
| SE_Done : forall ini,
    seq_execute ini Done ini.

(* Sequential execution relation is a partial function *)
Theorem seq_exec_deterministic : forall ini s fin1 fin2,
  seq_execute ini s fin1 ->
  seq_execute ini s fin2 ->
  fin1 = fin2.
Proof.
  intros ini s fin1 fin2 E1 E2; generalize dependent fin2;
  induction E1; intros fin2 E2; inversion E2; subst.
  - assert (mid = mid0) as EQ_mid;
    [ apply exec_deterministic with (ini := ini) (c := c)
    | apply IHE1; rewrite <- EQ_mid in H5 ]; assumption.
  - reflexivity.
Qed.

(* Sequential execution does not remove elements from the state *)
Theorem seq_exec_expansion : forall iniTPM ini s finTPM fin,
  seq_execute (iniTPM,ini) s (finTPM,fin) ->
  (iniTPM \subsetOf finTPM) /\ (ini \subsetOf fin).
Proof.
  intros iniTPM ini s finTPM fin E; split;
  generalize dependent fin; generalize dependent finTPM;
  generalize dependent ini; generalize dependent iniTPM;
  induction s; intros;
  inversion E; subst; try (intros m' I; assumption);
  destruct mid as [midTPM mid];
  assert (Inc : (iniTPM \subsetOf midTPM) /\ (ini \subsetOf mid)); 
  try (apply exec_expansion with (c := c); assumption).
  - apply Included_transitive with (st2 := midTPM);
    [ apply Inc
    | apply IHs with (ini := mid) (fin := fin); assumption ].
  - apply Included_transitive with (st2 := mid);
    [ apply Inc
    | apply IHs with (iniTPM := midTPM) (finTPM := finTPM); assumption ].
Qed.

(* Sequential execution cannot add a key to the state *)
Theorem seq_exec_cannotGenerateKey : forall s iniTPM ini finTPM fin k,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (privateKey k) finTPM ->
  In (privateKey k) iniTPM.
Proof.
  induction s; intros iniTPM ini finTPM fin k E I;
  inversion E; subst; try assumption; destruct mid as [midTPM mid];
  eapply exec_cannotGenerateKey; eauto.
Qed.


(* Sequential execution cannot add a random number to the state without an encrypted credential *)
Theorem seq_exec_cannotGenerateRand_contrapositive : forall s iniTPM ini finTPM fin g,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  ~ In (randomNum g) ini ->
  (forall n k, ~ In (encryptedCredential n g k) ini) ->
  ~ In (randomNum g) fin.
Proof.
  induction s; intros iniTPM ini finTPM fin g E Ng N.
  - destruct c; inversion E; inversion H2; 
    subst; eapply IHs; try fdeq;
    try (intros n0 k HC; inversion HC; try congruence; destruct (N n0 k); assumption);
    intros HC; inversion HC;
    [ inversion H; subst; destruct (N n (Public i r s1 d f)); assumption
    | congruence ].
  - inversion E; subst; congruence.
Qed.


(* Sequential execution cannot add an encrypted credential to the state without a random number *)
Theorem seq_exec_cannotGenerateCred_contrapositive : forall s iniTPM ini finTPM fin n g k,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  (forall n k, ~ In (encryptedCredential n g k) ini) ->
  ~ In (randomNum g) ini ->
  ~ In (encryptedCredential n g k) fin.
Proof.
  induction s; intros iniTPM ini finTPM fin n g k E Ne N;
  inversion E; subst; 
  [ destruct mid as [midTPM mid]; eapply IHs; eauto
  | intros HC; destruct (Ne n k); assumption];
  [ intros n0 k0; eapply exec_cannotGenerateCred_contrapositive; eauto
  | eapply exec_cannotGenerateRand_contrapositive; eauto].
Qed.











(* Message Inference *)
(* ***************** *)


Inductive inferrable : message -> state -> Prop :=
| I_publicKey : forall k,
    inferrable (publicKey k)
               [publicKey k]
| I_privateKey : forall k,
    inferrable (privateKey k)
               [privateKey k]
| I_hash : forall m,
    inferrable (hash m)
               [hash m]
| I_signature : forall m k st,
    inferrable m st ->
    inferrable (signature m k)
               (signature m k :: st)
| I_Attest : forall k,
    inferrable (TPM2B_Attest k)
               [TPM2B_Attest k ; publicKey k]
| I_encryptedCredential : forall n g k,
    inferrable (encryptedCredential n g k)
               [encryptedCredential n g k]
| I_randomNum : forall g,
    inferrable (randomNum g)
               [randomNum g]
| I_CSR_IDevID : forall id crt k st,
    inferrable (signedCertificate crt) st ->
    inferrable (TCG_CSR_IDevID id crt k)
               (TCG_CSR_IDevID id crt k :: publicKey k :: st)
| I_CSR_LDevID : forall m crt st1 st2,
    inferrable m st1 ->
    inferrable (signedCertificate crt) st2 ->
    inferrable (TCG_CSR_LDevID m crt) 
               (TCG_CSR_LDevID m crt :: st1 ++ st2)
| I_signedCertificate : forall k id k_ca,
    inferrable (signedCertificate (Cert k id k_ca)) 
               [signedCertificate (Cert k id k_ca) ; publicKey k]
| I_pair : forall m1 m2 st1 st2,
    inferrable m1 st1 ->
    inferrable m2 st2 -> 
    inferrable (pair m1 m2) 
               (pair m1 m2 :: st1 ++ st2).

Fixpoint inferFrom (msg : message) : state :=
  match msg with
  | signature m k => 
      (signature m k :: inferFrom m)
  | TPM2B_Attest k => 
      [TPM2B_Attest k ; publicKey k]
  | TCG_CSR_IDevID id (Cert k0 id0 k_ca) k => 
      [TCG_CSR_IDevID id (Cert k0 id0 k_ca) k ; publicKey k ; 
       signedCertificate (Cert k0 id0 k_ca) ; publicKey k0]
  | TCG_CSR_LDevID m (Cert k id k_ca) => 
      (TCG_CSR_LDevID m (Cert k id k_ca) :: inferFrom m ++ 
      [signedCertificate (Cert k id k_ca) ; publicKey k])
  | signedCertificate (Cert k id k_ca) => 
      [signedCertificate (Cert k id k_ca) ; publicKey k]
  | pair m1 m2 => 
      (pair m1 m2 :: inferFrom m1 ++ inferFrom m2)
  | _ => 
      [msg]
  end.

(* inferFrom function and inferrable relation are equivalent *)
Lemma inferFrom_iff_inferrable : forall m st,
  inferFrom m = st <-> inferrable m st.
Proof.
  intros m st; split; intros H.
  - generalize dependent m; assert (HI : forall m, inferrable m (inferFrom m)); intros m.
  -- induction m; simpl; try destruct c; try destruct s; 
     repeat constructor; assumption.
  -- intros H; induction m; subst; apply HI.
  - induction H; simpl; subst; try destruct crt; reflexivity.
Qed.


Fixpoint inferFromState (st : state) : state :=
  match st with
  | m :: st' => inferFrom m ++ inferFromState st'
  | _ => st
  end.
  













(* *************************** *)
(* Key Certification Protocols *)
(* *************************** *)
(* *************************** *)




(* Only public keys and certificates may reside in the initial state
   of the Owner and OEM *)
Definition needsGenerated (m : message) : Prop :=
  match m with
  | privateKey _ => True
  | hash _ => True
  | signature _ _ => True
  | TPM2B_Attest _ => True
  | encryptedCredential _ _ _ => True
  | randomNum _ => True
  | TCG_CSR_IDevID _ _ _ => True
  | TCG_CSR_LDevID _ _ => True
  | pair _ _ => True
  | _ => False
  end.


(* Only private keys may reside in the initial TPM state
   of the Owner and OEM *)
Definition needsGeneratedTPM (m : message) : Prop :=
  match m with
  | publicKey _ => True
  | hash _ => True
  | signature _ _ => True
  | TPM2B_Attest _ => True
  | encryptedCredential _ _ _ => True
  | randomNum _ => True
  | TCG_CSR_IDevID _ _ _ => True
  | TCG_CSR_LDevID _ _ => True
  | signedCertificate _ => True
  | pair _ _ => True
  | _ => False
  end.









(* Owner creation of LAK certificate based on IAK certificate *)
(* **************************************************************** *)


(*
... ;; MakePair csr sig ;; ...
*)
Fixpoint isSuperseqOfStep5_Owner (seq : sequence) (csr sig : message) : Prop :=
  match seq with
  | c ;; s =>
      match c with
      | MakePair m1 m2 =>
          if (decEq csr m1)
          then (
            if (decEq sig m2)
            then True (* Done *)
            else isSuperseqOfStep5_Owner s csr sig )
          else isSuperseqOfStep5_Owner s csr sig
      | _ => isSuperseqOfStep5_Owner s csr sig
      end
  | Done => False
  end.

Lemma isSuperseqOfStep5_Owner_lemma : forall s iniTPM ini finTPM fin csr sig,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (pair csr sig) fin ->
  ~ (In (pair csr sig) ini) ->
  isSuperseqOfStep5_Owner s csr sig.
Proof.
  induction s; intros iniTPM ini finTPM fin csr sig E I N0.
  - destruct c; simpl in *; inversion E; inversion H2; 
    subst; try (eapply IHs; fdeq);
    destruct (decEq csr m);
    destruct (decEq sig m0);
    subst; trivial;
    eapply IHs; fdeq.
  - inversion E; subst; congruence.
Qed.


(*
... ;; TPM2_Sign hsh (pubToPrivKey lak) ;; 
... ;; MakePair csr (signature hsh (pubToPrivKey lak)) ;; ...
*)
Fixpoint isSuperseqOfSteps4to5_Owner (seq : sequence) (hsh csr : message) (lak : pubKey) : Prop :=
  match seq with
  | c ;; s =>
      match c with
      | TPM2_Sign m k =>
          if (decEq hsh m)
          then (
            if (decEq (pubToPrivKey lak) k)
            then isSuperseqOfStep5_Owner s csr (signature hsh (pubToPrivKey lak))  (* Find next *)
            else isSuperseqOfSteps4to5_Owner s hsh csr lak )
          else isSuperseqOfSteps4to5_Owner s hsh csr lak
      | _ => isSuperseqOfSteps4to5_Owner s hsh csr lak
      end
  | Done => False
  end.

Lemma isSuperseqOfSteps4to5_Owner_lemma : forall s iniTPM ini finTPM fin hsh csr lak,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (pair csr (signature hsh (pubToPrivKey lak))) fin ->
  ~ (In (pair csr (signature hsh (pubToPrivKey lak))) ini) ->
  ~ (In (signature hsh (pubToPrivKey lak)) ini) ->
  (forall k, hsh <> TPM2B_Attest k) ->
  isSuperseqOfSteps4to5_Owner s hsh csr lak.
Proof.
  induction s; intros iniTPM ini finTPM fin hsh csr lak E I N0 N1 NA.
  - destruct c; simpl in *; inversion E; inversion H2; 
    subst; try (eapply IHs; fdeq);
    destruct (decEq hsh m);
    try destruct (decEq (pubToPrivKey lak) (Private i Restricting Signing d f));
    try destruct (decEq (pubToPrivKey lak) (Private i NonRestricting Signing d f));
    subst; try eapply IHs; try eapply isSuperseqOfStep5_Owner_lemma; fdeq.
  - inversion E; subst; congruence.
Qed.


(*
... ;; TPM2_Hash csr ;;
... ;; TPM2_Sign (hash csr) (pubToPrivKey lak) ;;
... ;; MakePair csr (signature (hash csr) (pubToPrivKey lak)) ;; ...
*)
Fixpoint isSuperseqOfSteps3to5_Owner (seq : sequence) (csr : message) (lak : pubKey) : Prop :=
  match seq with
  | c ;; s => 
      match c with 
      | TPM2_Hash m => 
          if (decEq csr m)
          then isSuperseqOfSteps4to5_Owner s (hash m) m lak (* Find next *)
          else isSuperseqOfSteps3to5_Owner s csr lak
      | _ => isSuperseqOfSteps3to5_Owner s csr lak
      end
  | Done => False
  end.

Lemma isSuperseqOfSteps3to5_Owner_lemma : forall s iniTPM ini finTPM fin csr lak,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (pair csr (signature (hash csr) (pubToPrivKey lak))) fin ->
  ~ (In (pair csr (signature (hash csr) (pubToPrivKey lak))) ini) ->
  ~ (In (signature (hash csr) (pubToPrivKey lak)) ini) ->
  ~ (In (hash csr) ini) ->
  ~ (In (hash csr) iniTPM) ->
  isSuperseqOfSteps3to5_Owner s csr lak.
Proof.
  induction s; intros iniTPM ini finTPM fin csr lak E I N0 N1 N2 N3.
  - destruct c; simpl in *; inversion E; inversion H2; 
    subst; try (eapply IHs; fdeq);
    destruct (decEq csr m);
    subst; try eapply IHs; try eapply isSuperseqOfSteps4to5_Owner_lemma; fdeq.
  - inversion E; subst; congruence.
Qed.


(*
... ;; MakeCSR_LDevID attest cert ;;
... ;; TPM2_Hash (TCG_CSR_LDevID attest cert) ;;
... ;; TPM2_Sign (hash (TCG_CSR_LDevID attest cert)) (pubToPrivKey lak) ;;
... ;; MakePair (TCG_CSR_LDevID attest cert) 
                (signature (hash (TCG_CSR_LDevID attest cert)) (pubToPrivKey lak)) ;; ...
*)
Fixpoint isSuperseqOfSteps2to5_Owner (seq : sequence) (attest : message) (cert : signedCert) (lak : pubKey) : Prop :=
  match seq with
  | c ;; s => 
      match c with
      | MakeCSR_LDevID m crt => 
          if (decEq attest m) 
          then (
            if (decEq cert crt)
            then isSuperseqOfSteps3to5_Owner s (TCG_CSR_LDevID m crt) lak (* Find next *)
            else isSuperseqOfSteps2to5_Owner s attest cert lak )
          else isSuperseqOfSteps2to5_Owner s attest cert lak
      | _ => isSuperseqOfSteps2to5_Owner s attest cert lak
      end
  | Done => False
  end.

Lemma isSuperseqOfSteps2to5_Owner_lemma : forall s iniTPM ini finTPM fin attest cert lak,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (pair (TCG_CSR_LDevID attest cert)
           (signature (hash (TCG_CSR_LDevID attest cert)) (pubToPrivKey lak))) fin ->
  ~ (In (pair (TCG_CSR_LDevID attest cert)
              (signature (hash (TCG_CSR_LDevID attest cert)) (pubToPrivKey lak))) ini) ->
  ~ (In (signature (hash (TCG_CSR_LDevID attest cert)) (pubToPrivKey lak)) ini) ->
  ~ (In (hash (TCG_CSR_LDevID attest cert)) ini) ->
  ~ (In (hash (TCG_CSR_LDevID attest cert)) iniTPM) ->
  ~ (In (TCG_CSR_LDevID attest cert) ini) ->
  isSuperseqOfSteps2to5_Owner s attest cert lak.
Proof.
  induction s; intros iniTPM ini finTPM fin attest cert lak E I N0 N1 N2 N2_TPM N3.
  - destruct c; simpl in *; inversion E; inversion H2; 
    subst; try (eapply IHs; fdeq).
    destruct (decEq attest m);
    destruct (decEq cert s0);
    subst; try eapply IHs; try eapply isSuperseqOfSteps3to5_Owner_lemma; fdeq.
  - inversion E; subst; congruence.
Qed.


(*
... ;; TPM2_Certify lak (pubToPrivKey iak) ;;
... ;; MakeCSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert ;;
... ;; TPM2_Hash 
          (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert) ;;
... ;; TPM2_Sign 
          (hash (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert)) 
          (pubToPrivKey lak) ;;
... ;; MakePair 
          (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert) 
          (signature 
            (hash (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert)) 
            (pubToPrivKey lak)) ;; ...
*)
Fixpoint isSuperseqOfSteps1to5_Owner (seq : sequence) (iak lak : pubKey) (cert : signedCert) : Prop :=
  match seq with
  | c ;; s => 
      match c with
      | TPM2_Certify k k0' => 
          if (decEq lak k)
          then (
            if (decEq (pubToPrivKey iak) k0')
            then isSuperseqOfSteps2to5_Owner s (signature (TPM2B_Attest k) k0') cert k  (* Find next *)
            else isSuperseqOfSteps1to5_Owner s iak lak cert )
          else isSuperseqOfSteps1to5_Owner s iak lak cert
      | _ => isSuperseqOfSteps1to5_Owner s iak lak cert
      end
  | Done => False
  end.

Lemma isSuperseqOfSteps1to5_Owner_lemma : forall s iniTPM ini finTPM fin iak lak cert,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (pair (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert)
           (signature 
              (hash (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert)) 
              (pubToPrivKey lak))) fin ->
  ~ (In (pair (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert)
              (signature 
                  (hash (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert)) 
                  (pubToPrivKey lak))) ini) ->
  ~ (In (signature 
          (hash (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert)) 
          (pubToPrivKey lak)) ini) ->
  ~ (In (hash (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert)) ini) ->
  ~ (In (hash (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert)) iniTPM) ->
  ~ (In (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert) ini) ->
  ~ (In (signature (TPM2B_Attest lak) (pubToPrivKey iak)) ini) ->
  ~ (In (TPM2B_Attest lak) ini) ->
  ~ (In (TPM2B_Attest lak) iniTPM) ->
  isSuperseqOfSteps1to5_Owner s iak lak cert.
Proof.
  induction s; intros iniTPM ini finTPM fin iak lak cert E I N0 N1 N2 N2_TPM N3 N4 N5 N5_TPM.
  - destruct c; simpl in *; inversion E; inversion H2;  
    subst; try (eapply IHs; fdeq).
    destruct (decEq lak (Public i r s1 d f));
    destruct (decEq (pubToPrivKey iak) (Private i0 r0 Signing d0 f0));
    subst; try eapply IHs; try eapply isSuperseqOfSteps2to5_Owner_lemma; try fdeq;
    try (rewrite <- e0; assumption).
  - inversion E; subst; congruence.
Qed.



Module Type LAK_Cert_Protocol.


(* Owner parameters *)
  Parameter pubLAK : pubKey.
  Parameter pubIAK : pubKey.
  Parameter certIAK : signedCert.

(* CA parameters *)
  Parameter pubCA : pubKey.
  Parameter pubOEM : pubKey.

(* All keys must be distinct *)
  Axiom keys_distinct :
    pubLAK <> pubIAK /\
    pubLAK <> pubCA /\
    pubLAK <> pubOEM /\
    pubIAK <> pubCA /\
    pubIAK <> pubOEM /\
    pubCA <> pubOEM.

  Definition privLAK := pubToPrivKey pubLAK.
  Definition privIAK := pubToPrivKey pubIAK.
  Definition privCA := pubToPrivKey pubCA.





(* Correct protocol steps of owner *)
  Definition steps1to5_Owner : sequence :=
    TPM2_Certify pubLAK privIAK ;;
    MakeCSR_LDevID (signature (TPM2B_Attest pubLAK) privIAK) certIAK ;;
    TPM2_Hash (TCG_CSR_LDevID (signature (TPM2B_Attest pubLAK) privIAK) certIAK) ;;
    TPM2_Sign (hash (TCG_CSR_LDevID (signature (TPM2B_Attest pubLAK) privIAK) certIAK)) privLAK ;;
    MakePair (TCG_CSR_LDevID (signature (TPM2B_Attest pubLAK) privIAK) certIAK) 
             (signature (hash (TCG_CSR_LDevID (signature (TPM2B_Attest pubLAK) privIAK) certIAK)) privLAK) ;;
    Done.



(* The CA is trusted to have a good initial state *)
Definition iniTPM_CA : tpm_state :=
  [ privateKey privCA ;
    publicKey pubCA ].

  Definition ini_CA : state :=
  [ publicKey pubOEM ;
    privateKey privCA ;
    publicKey pubCA ].

  Axiom CA_keys_good :
    caKey pubCA /\
    caKey pubOEM.

(* Protocol steps of CA *)
(* The CA waits to recieve a message from the owner. *)
(* That message must be in a specific form to be considered a proper request. *)
(* The CA will then execute its protocol steps on the input message. *)
(* If the protocol succeeds the CA will issue certificate [Cert k_LAK id privCA] to the owner. *)
  Definition steps_CA (msg : message) (iak lak : pubKey) (cert : signedCert) : Prop :=
    match msg with
    | (pair (TCG_CSR_LDevID (signature (TPM2B_Attest k) k0') 
                            (Cert k0 id k_ca'))
            (signature m k')) =>
          iak = k0 /\
          lak = k /\
          cert = (Cert k0 id k_ca') /\
          seq_execute (iniTPM_CA, inferFrom msg ++ ini_CA)
                            (CheckHash m
                                      (TCG_CSR_LDevID (signature (TPM2B_Attest k) k0') 
                                                      (Cert k0 id k_ca')) ;;
                            CheckSig (signature m k') k ;;
                            CheckSig (signature (TPM2B_Attest k) k0') k0 ;;
                            CheckCert (Cert k0 id k_ca') pubOEM ;;
                            CheckAttributes k Restricting Signing NonDecrypting Fixing ;;
                            Done)
                            (iniTPM_CA, 
                            inferFrom msg ++ ini_CA)
    | _ => False
    end.





(* Minimal initial state pair of owner *)

  Definition iniTPM_Owner : tpm_state :=
  [ privateKey privLAK ;
    privateKey privIAK ].

  Definition ini_Owner : state :=
  [ signedCertificate certIAK ].



(* Minimality proof part 1 *)
  Lemma ini_Owner_lowerBound : forall iniTPM ini fin,
    seq_execute (iniTPM, ini) steps1to5_Owner fin ->
    (iniTPM_Owner \subsetOf iniTPM) /\
    (ini_Owner \subsetOf ini).
  Proof.
    intros iniTPM ini fin E;
(* Split steps_Owner into its individual commands *)
    inversion E as [initial mid1 final command steps_Owner' H_Certify E1| ]; subst;
    inversion E1 as [initial mid2 final command steps_Owner' H_MakeCSR E2| ]; subst;
    inversion E2 as [initial mid3 final command steps_Owner' H_Hash E3| ]; subst;
    inversion E3 as [initial mid4 final command steps_Owner' H_Sign E4| ]; subst;
    inversion E4 as [initial mid5 final command steps_Owner' H_MakePair E5| ]; subst;
    inversion E5; subst;
(* Invert each individual step in reverse order *) 
    inversion H_MakePair; subst; 
    inversion H_Sign; subst;
    inversion H_Hash; subst;
    inversion H_MakeCSR; subst;
    inversion H_Certify; subst;
(* Clear all hypothesis other than state requirements and key definitions *)
    clear E E1 E2 E3 E4 E5;
    clear H_Certify H_MakeCSR H_Hash H_Sign H_MakePair;
    split.
(* Case TPM state with Restricted Signing key *)
    - unfold iniTPM_Owner; intros m I; inversion I; subst.
    -- rewrite <- H0; inversion H5 as [EQ_false | H5']; subst.
        inversion EQ_false.
        assumption.
    -- inversion H; subst.
    --- rewrite <- H10; assumption.
    --- inversion H1.
(* Case state with Restricted Signing key *)
    - unfold ini_Owner; intros m I; inversion I; subst.
    -- inversion H11 as [EQ_false | H11']; subst.
        inversion EQ_false.
        assumption.
    -- inversion H.
(* Case TPM state with Non-Restricted Signing key *)
    - unfold iniTPM_Owner; intros m I; inversion I; subst.
    -- rewrite <- H0; inversion H5 as [EQ_false | H5']; subst. 
        inversion EQ_false.
        assumption.
    -- inversion H; subst.
    --- rewrite <- H10; assumption.
    --- inversion H1.
(* Case state with Non-Restricted Signing key *)
    - unfold ini_Owner; intros m I; inversion I; subst.
    -- inversion H11 as [EQ_false | H11']; subst. 
         inversion EQ_false.
         assumption.
    -- inversion H.
  Qed.





(* Minimality proof part 2 *)
  Lemma ini_Owner_sufficient : forall msg,
    attestationKey pubIAK ->
    steps_CA msg pubIAK pubLAK certIAK ->
    exists fin, seq_execute (iniTPM_Owner, ini_Owner) steps1to5_Owner fin.
  Proof. 
    intros m goodIAK CA;
    unfold iniTPM_Owner, ini_Owner, steps1to5_Owner, privIAK, privLAK;
    destruct pubIAK, r, s, d, f; simpl in goodIAK; try inversion goodIAK;
    destruct m; try inversion CA;
    destruct m1; try inversion CA;
    destruct m1; try inversion CA;
    destruct m1; try inversion CA;
    destruct s; try inversion CA;
    destruct m2; try inversion CA; subst;
    destruct H0; subst; destruct H0; subst;
    clear CA; simpl in *;
    inversion H0 as [initial mid1 final command steps_Owner' H_CheckHash H1 | ]; subst; 
    inversion H1 as [initial mid2 final command steps_Owner' H_CheckSig1 H2 | ]; subst;
    inversion H2 as [initial mid3 final command steps_Owner' H_CheckSig2 H3 | ]; subst;
    inversion H3 as [initial mid4 final command steps_Owner' H_CheckCert H4 | ]; subst;
    inversion H4 as [initial mid5 final command steps_Owner' H_CheckAttributes H5 | ]; subst;
    inversion H5; subst;
    inversion H_CheckAttributes; subst;
    simpl; trivial;
    eexists; simpl; repeat eapply SE_Seq; econstructor; simpl; auto.
  Qed.


  Axiom correct_Owner : forall finTPM fin,
    seq_execute (iniTPM_Owner, ini_Owner) steps1to5_Owner (finTPM, fin) ->
    exists msg, In msg fin /\ steps_CA msg pubIAK pubLAK certIAK.



  Lemma ca_implies_isSuperseqOfSteps1to5 : forall s iniTPM ini finTPM fin msg iak lak cert,
    seq_execute (iniTPM, ini) s (finTPM, fin) ->
    In msg fin ->
    (forall m', needsGeneratedTPM m' -> ~ In m' iniTPM) ->
    (forall m', needsGenerated m' -> ~ In m' ini) ->
    steps_CA msg iak lak cert -> 
    isSuperseqOfSteps1to5_Owner s iak lak cert.
  Proof.
    intros s iniTPM ini finTPM fin m iak lak cert E I N_TPM N CA.
(* Get m into the form of the match statement in steps_CA *)
    destruct m; try inversion CA;
    destruct m1; try inversion CA;
    destruct m1; try inversion CA;
    destruct m1; try inversion CA;
    destruct s0; try inversion CA;
    destruct m2; try inversion CA; subst;
    destruct H0; subst; destruct H0; subst;
    clear CA; simpl in *.
(* Split steps_CA into its individual commands *)
    inversion H0 as [initial mid1 final command steps_Owner' H_CheckHash H1 | ]; subst; 
    inversion H1 as [initial mid2 final command steps_Owner' H_CheckSig1 H2 | ]; subst;
    inversion H2 as [initial mid3 final command steps_Owner' H_CheckSig2 H3 | ]; subst;
    inversion H3 as [initial mid4 final command steps_Owner' H_CheckCert H4 | ]; subst;
    inversion H4 as [initial mid5 final command steps_Owner' H_CheckAttributes H5 | ]; subst;
    inversion H5; subst;
(* Invert each individual step in reverse order *) 
    inversion H_CheckAttributes; subst;
    inversion H_CheckCert; subst;
    inversion H_CheckSig2; subst;
    inversion H_CheckSig1; subst;
    inversion H_CheckHash; subst.
(* Apply lemma *)
    eapply isSuperseqOfSteps1to5_Owner_lemma; eauto; 
    try apply N; try apply N_TPM; simpl; trivial.
  Qed.



  Lemma isSuperseqOfSteps1to5_implies_certify : forall s iak lak cert,
    isSuperseqOfSteps1to5_Owner s iak lak cert ->
    command_in_sequence (TPM2_Certify lak (pubToPrivKey iak)) s.
  Proof.
    induction s; intros iak lak cert H0.
    - simpl; destruct (decEq (TPM2_Certify lak (pubToPrivKey iak)) c);
      [ trivial
      | apply IHs with (cert := cert);
        destruct c; simpl in *; try fdeq ].
      destruct (decEq lak p); 
      destruct (decEq (pubToPrivKey iak) p0); subst; congruence.
    - inversion H0.
  Qed.
(*
  Lemma isSuperseqOfSteps1to5_Owner_implies_sign : forall s iak lak cert,
    isSuperseqOfSteps1to5_Owner s iak lak cert ->
    exists hsh, command_in_sequence s (TPM2_Sign hsh (pubToPrivKey lak)).
  Proof.
    intros s iak lak cert H0.
    exists (hash (TCG_CSR_LDevID (signature (TPM2B_Attest pubLAK) privIAK) certIAK)).
    generalize dependent cert. generalize dependent lak. generalize dependent iak.
    induction s; intros.
    simpl. destruct (decEq
    (TPM2_Sign
       (hash
          (TCG_CSR_LDevID
             (signature (TPM2B_Attest pubLAK) privIAK) certIAK))
       (pubToPrivKey lak)) c).
       trivial.
      eapply IHs. destruct c; try (simpl in *; fdeq; fail). simpl in *.
      destruct (decEq lak p);
      destruct (decEq (pubToPrivKey iak) p0); subst; try congruence.
*)
  Lemma certify_implies_lakInTPM : forall s iniTPM ini finTPM fin iak lak,
    seq_execute (iniTPM, ini) s (finTPM, fin) -> 
    command_in_sequence (TPM2_Certify lak (pubToPrivKey iak)) s ->
    In (privateKey (pubToPrivKey lak)) iniTPM.
  Proof.
    induction s; intros iniTPM ini finTPM fin iak lak E CI.
    - simpl in *; destruct (decEq (TPM2_Certify lak (pubToPrivKey iak)) c); inversion E; subst.
    -- inversion H2; assumption.
    -- destruct mid as [midTPM mid]; eapply exec_cannotGenerateKey; eauto.
    - inversion CI.
  Qed.


  Lemma certify_implies_iakInTPM : forall s iniTPM ini finTPM fin iak lak,
    seq_execute (iniTPM, ini) s (finTPM, fin) -> 
    command_in_sequence (TPM2_Certify lak (pubToPrivKey iak)) s ->
    In (privateKey (pubToPrivKey iak)) iniTPM.
  Proof.
    induction s; intros iniTPM ini finTPM fin iak lak E CI.
    - simpl in *; destruct (decEq (TPM2_Certify lak (pubToPrivKey iak)) c); inversion E; subst.
    -- inversion H2; assumption.
    -- destruct mid as [midTPM mid]; eapply exec_cannotGenerateKey; eauto.
    - inversion CI.
  Qed.




(* PROTOCOL ASSURANCES *)

(* Given the following assumptions: 
      The Owner executes some sequence of steps
      resulting in a message in its final state
      when only keys and certificates may be in its initial states.
      The CA's protocol executes successfully on the given message.
  Conclude:
      The private IAK and private LAK reside in the same TPM *)
  Theorem lak_and_iak_in_TPM : forall s iniTPM ini finTPM fin msg iak lak cert,
    seq_execute (iniTPM, ini) s (finTPM, fin) -> 
    In msg fin ->
    (forall m', needsGeneratedTPM m' -> ~ In m' iniTPM) ->
    (forall m', needsGenerated m' -> ~ In m' ini) ->
    steps_CA msg iak lak cert ->
    In (privateKey (pubToPrivKey lak)) iniTPM /\ In (privateKey (pubToPrivKey iak)) iniTPM.
  Proof.
    intros s iniTPM ini finTPM fin m iak lak cert E I N_TPM N CA; 
    split; [ eapply certify_implies_lakInTPM | eapply certify_implies_iakInTPM ];
    eauto; eapply isSuperseqOfSteps1to5_implies_certify; eapply ca_implies_isSuperseqOfSteps1to5; eauto.
  Qed.

(* Conclude:
      The LAK is a Restricted Signing NonDecrypting key *)
    Theorem lak_good_attributes : forall msg iak lak cert,
      steps_CA msg iak lak cert ->
      attestationKey lak.
    Proof.
      intros m iak lak cert CA;
      destruct m; try inversion CA;
      destruct m1; try inversion CA;
      destruct m1; try inversion CA;
      destruct m1; try inversion CA;
      destruct s; try inversion CA;
      destruct m2; try inversion CA; subst;
      destruct H0; subst; destruct H0; subst;
      clear CA; simpl in *.
      inversion H0 as [initial mid1 final command steps_Owner' H_CheckHash H1 | ]; subst; 
      inversion H1 as [initial mid2 final command steps_Owner' H_CheckSig1 H2 | ]; subst;
      inversion H2 as [initial mid3 final command steps_Owner' H_CheckSig2 H3 | ]; subst;
      inversion H3 as [initial mid4 final command steps_Owner' H_CheckCert H4 | ]; subst;
      inversion H4 as [initial mid5 final command steps_Owner' H_CheckAttributes H5 | ]; subst;
      inversion H5; subst;
      inversion H_CheckAttributes; subst;
      simpl; trivial.
    Qed.


  


(*
  Theorem control_of_lak : forall s iniTPM ini finTPM fin m iak lak cert,
    seq_execute (iniTPM, ini) s (finTPM, fin) -> 
    In m fin ->
    (forall m', needsGenerated m' -> ~ In m' iniTPM) ->
    (forall m', needsGenerated m' -> ~ In m' ini) ->
    steps_CA m iak lak cert ->
    exists hsh, command_in_sequence s (TPM2_Sign hsh (pubToPrivKey lak)).
*)

End LAK_Cert_Protocol.





(*
Module goodLAK <: LAK_Cert_Protocol.

(* Owner parameters *)
  Definition pubNewKey : pubKey := Public 52 Restricting Signing NonDecrypting.
  Definition pubIAK : pubKey := Public 51 Restricting Signing NonDecrypting.
  Definition certIAK : signedCert := Cert (Public 51 Restricting Signing NonDecrypting) (Device_info 5) (Private 1 NonRestricting Signing NonDecrypting).

(* CA parameters *)
  Definition pubCA : pubKey := Public 2 NonRestricting Signing NonDecrypting.
  Definition privCA : privKey := Private 2 NonRestricting Signing NonDecrypting.
  Definition pubOEM : pubKey := Public 1 NonRestricting Signing NonDecrypting.


  Theorem keys_distinct :
    pubNewKey <> pubIAK /\
    pubNewKey <> pubCA /\
    pubNewKey <> pubOEM /\
    pubIAK <> pubCA /\
    pubIAK <> pubOEM /\
    pubCA <> pubOEM.
  Proof.
    repeat split; intros contra; inversion contra.
  Qed.


  Definition privLAK := pubToPrivKey pubNewKey.
  Definition privIAK := pubToPrivKey pubIAK.


  Definition iniTPM_Owner : tpm_state :=
  [ privateKey privLAK ;
    privateKey privIAK ].

  Definition ini_Owner : state :=
  [ publicKey pubNewKey ;
    signedCertificate certIAK ].


  Definition steps_Owner : sequence :=
  TPM2_Certify pubNewKey privIAK ;;
  MakeCSR_LDevID (signature (TPM2B_Attest pubNewKey) privIAK) certIAK ;;
  TPM2_Hash (TCG_CSR_LDevID (signature (TPM2B_Attest pubNewKey) privIAK) certIAK) ;;
  TPM2_Sign (hash (TCG_CSR_LDevID (signature (TPM2B_Attest pubNewKey) privIAK) certIAK)) privLAK ;;
  MakePair (TCG_CSR_LDevID (signature (TPM2B_Attest pubNewKey) privIAK) certIAK) 
           (signature (hash (TCG_CSR_LDevID (signature (TPM2B_Attest pubNewKey) privIAK) certIAK)) privIAK) ;;
  Done.




  Theorem steps_lowerBound : forall iniTPM ini fin,
    seq_execute (iniTPM, ini) steps_Owner fin ->
    (iniTPM_Owner \subsetOf iniTPM) /\
    (ini_Owner \subsetOf ini).
  Proof.
    intros iniTPM ini fin E.

    inversion E as [initial mid1 final command steps_Owner' E_Certify E'| ]; subst. 
    inversion E' as [initial mid2 final command steps_Owner' E_MakeCSR E''| ]; subst.
    inversion E'' as [initial mid3 final command steps_Owner' E_Hash E'''| ]; subst.
    inversion E''' as [initial mid4 final command steps_Owner' E_Sign E''''| ]; subst.
    inversion E'''' as [initial mid5 final command steps_Owner' E_MakePair E'''''| ]; subst.
    inversion E'''''; subst.

    inversion E_MakePair; subst; 
    inversion E_Sign; subst;
    inversion E_Hash; subst;
    inversion E_MakeCSR; subst;
    inversion E_Certify; subst;

    clear E E' E'' E''' E'''' E''''';
    clear E_Certify E_MakeCSR E_Hash E_Sign E_MakePair;
    split.

    - unfold iniTPM_Owner; intros m I; inversion I; subst.
    -- unfold privIAK; simpl; inversion H3 as [EQ_false | H3']; subst.
        inversion EQ_false.
       inversion H3' as [EQ_false | H3'']; subst. 
        inversion EQ_false.
        assumption.
    -- inversion H; subst.
    --- unfold privIAK; simpl. assumption.
    --- inversion H0.

    - unfold ini_Owner; intros m I; inversion I; subst.
    -- unfold pubNewKey; simpl; assumption.
    -- inversion H; subst.
    --- inversion H10 as [EQ_false | H10']; subst. 
         inversion EQ_false.
         assumption.
    --- inversion H0.
Qed.




  Theorem steps_min : exists fin,
    seq_execute (iniTPM_Owner, ini_Owner) steps_Owner fin.
  Proof.
    eexists; unfold iniTPM_Owner; unfold ini_Owner; unfold steps_Owner;
    unfold privIAK; unfold privIAK; unfold certIAK;
    unfold pubNewKey; unfold pubIAK.
    repeat eapply E_Seq; constructor; simpl; auto.
  Qed.




  Definition iniTPM_CA : tpm_state :=
  [ privateKey privCA ;
    publicKey pubCA ].

  Definition ini_CA : state :=
  [ publicKey pubOEM ;
    privateKey privCA ;
    publicKey pubCA ].

  Theorem CA_keys_good :
    privCA = pubToPrivKey pubCA /\
    caKey pubCA /\
    caKey pubOEM.
  Proof. 
    repeat split.
  Qed.



  Definition steps_CA (m : message) : Prop :=
    match m with
    | ((TCG_CSR_LDevID (signature (TPM2B_Attest k) k_IAK') 
                       (Cert k_IAK id k_OEM')),,
       (signature m k')) =>
          seq_execute (iniTPM_CA, inferFrom m ++ ini_CA)
                           (CheckHash m 
                                     (TCG_CSR_LDevID (signature (TPM2B_Attest k) k_IAK') 
                                                     (Cert k_IAK id k_OEM')) ;;
                            CheckSig (signature m k') k ;;
                            CheckSig (signature (TPM2B_Attest k) k_IAK') k_IAK ;;
                            CheckCert (Cert k_IAK id k_OEM') pubOEM ;;
                            CheckAttributes k Restricting Signing NonDecrypting ;;
                            Done)
                           (iniTPM_CA, 
                            inferFrom m ++ ini_CA)
    | _ => False
    end.


  Theorem correct_Owner : forall finTPM fin,
    seq_execute (iniTPM_Owner, ini_Owner) steps_Owner (finTPM, fin) ->
    exists m, In m fin /\ steps_CA m.
  Proof.
    intros finTPM fin E. 
    exists ((TCG_CSR_LDevID (signature (TPM2B_Attest pubNewKey) privIAK) certIAK) ,,
            (signature (hash (TCG_CSR_LDevID (signature (TPM2B_Attest pubNewKey) privIAK) certIAK)) privIAK)).
    split.
    - inversion E as [initial mid1 final command steps_Owner' E_Certify E'| ]; subst. 
      inversion E' as [initial mid2 final command steps_Owner' E_MakeCSR E''| ]; subst.
      inversion E'' as [initial mid3 final command steps_Owner' E_Hash E'''| ]; subst.
      inversion E''' as [initial mid4 final command steps_Owner' E_Sign E''''| ]; subst.
      inversion E'''' as [initial mid5 final command steps_Owner' E_MakePair E'''''| ]; subst.
      inversion E'''''; subst.
      inversion E_MakePair; subst; 
      inversion E_Sign; subst;
      inversion E_Hash; subst;
      inversion E_MakeCSR; subst;
      inversion E_Certify; subst;
      clear.
      simpl; auto.
    - unfold iniTPM_Owner; unfold ini_Owner; unfold steps_Owner;
      unfold privIAK; unfold privIAK; unfold certIAK;
      unfold pubNewKey; unfold pubIAK. simpl.
      repeat eapply E_Seq; constructor; simpl; auto 11.
  Qed.


End goodLAK.
*)








(* OEM creation of IAK certificate based on EK certificate *)
(* ******************************************************* *)



(*
... ;; MakePair csr sig ;; ...
*)
Fixpoint isSuperseqOfStep4_OEM (seq : sequence) (csr sig : message) : Prop :=
  match seq with
  | c ;; s =>
      match c with
      | MakePair m1 m2 =>
          if (decEq csr m1)
          then (
            if (decEq sig m2)
            then True (* Done *)
            else isSuperseqOfStep4_OEM s csr sig )
          else isSuperseqOfStep4_OEM s csr sig
      | _ => isSuperseqOfStep4_OEM s csr sig
      end
  | Done => False
  end.

Lemma isSuperseqOfStep4_OEM_lemma : forall s iniTPM ini finTPM fin csr sig,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (pair csr sig) fin ->
  ~ (In (pair csr sig) ini) ->
  isSuperseqOfStep4_OEM s csr sig.
Proof.
  induction s; intros iniTPM ini finTPM fin csr sig E I N0.
  - destruct c; simpl in *; inversion E; inversion H2; 
    subst; try (eapply IHs; fdeq);
    destruct (decEq csr m);
    destruct (decEq sig m0);
    subst; trivial; eapply IHs; fdeq.
  - inversion E; subst; congruence.
Qed.


(*
... ;; TPM2_Sign hsh (pubToPrivKey iak) ;; 
... ;; MakePair csr (signature hsh (pubToPrivKey iak)) ;; ...
*)
Fixpoint isSuperseqOfSteps3to4_OEM (seq : sequence) (hsh csr : message) (iak : pubKey) : Prop :=
  match seq with
  | c ;; s =>
      match c with
      | TPM2_Sign m k =>
          if (decEq hsh m)
          then (
            if (decEq (pubToPrivKey iak) k)
            then isSuperseqOfStep4_OEM s csr (signature hsh (pubToPrivKey iak))  (* Find next *)
            else isSuperseqOfSteps3to4_OEM s hsh csr iak )
          else isSuperseqOfSteps3to4_OEM s hsh csr iak
      | _ => isSuperseqOfSteps3to4_OEM s hsh csr iak
      end
  | Done => False
  end.

Lemma isSuperseqOfSteps3to4_OEM_lemma : forall s iniTPM ini finTPM fin hsh csr iak,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (pair csr (signature hsh (pubToPrivKey iak))) fin ->
  ~ (In (pair csr (signature hsh (pubToPrivKey iak))) ini) ->
  ~ (In (signature hsh (pubToPrivKey iak)) ini) ->
  (forall k, hsh <> TPM2B_Attest k) ->
  isSuperseqOfSteps3to4_OEM s hsh csr iak.
Proof.
  induction s; intros iniTPM ini finTPM fin hsh csr iak E I N0 N1 NA.
  - destruct c; simpl in *; inversion E; inversion H2; 
    subst; try (eapply IHs; fdeq);
    destruct (decEq hsh m);
    try destruct (decEq (pubToPrivKey iak) (Private i Restricting Signing d f));
    try destruct (decEq (pubToPrivKey iak) (Private i NonRestricting Signing d f));
    subst; try eapply IHs; try eapply isSuperseqOfStep5_Owner_lemma; fdeq.
  - inversion E; subst; congruence.
Qed.


(*
... ;; TPM2_Hash csr ;;
... ;; TPM2_Sign (hash csr) (pubToPrivKey iak) ;;
... ;; MakePair csr (signature (hash csr) (pubToPrivKey iak)) ;; ...
*)
Fixpoint isSuperseqOfSteps2to4_OEM (seq : sequence) (csr : message) (iak : pubKey) : Prop :=
  match seq with
  | c ;; s => 
      match c with 
      | TPM2_Hash m => 
          if (decEq csr m)
          then isSuperseqOfSteps3to4_OEM s (hash m) m iak (* Find next *)
          else isSuperseqOfSteps2to4_OEM s csr iak
      | _ => isSuperseqOfSteps2to4_OEM s csr iak
      end
  | Done => False
  end.

Lemma isSuperseqOfSteps2to4_OEM_lemma : forall s iniTPM ini finTPM fin csr iak,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (pair csr (signature (hash csr) (pubToPrivKey iak))) fin ->
  ~ (In (pair csr (signature (hash csr) (pubToPrivKey iak))) ini) ->
  ~ (In (signature (hash csr) (pubToPrivKey iak)) ini) ->
  ~ (In (hash csr) ini) ->
  ~ (In (hash csr) iniTPM) ->
  isSuperseqOfSteps2to4_OEM s csr iak.
Proof.
  induction s; intros iniTPM ini finTPM fin csr iak E I N0 N1 N2 N3.
  - destruct c; simpl in *; inversion E; inversion H2; 
    subst; try (eapply IHs; fdeq);
    destruct (decEq csr m);
    subst; try eapply IHs; try eapply isSuperseqOfSteps4to5_Owner_lemma; fdeq.
  - inversion E; subst; congruence.
Qed.


(*
... ;; MakeCSR_IDevID ident cert iak ;;
... ;; TPM2_Hash (TCG_CSR_IDevID ident cert iak) ;;
... ;; TPM2_Sign (hash (TCG_CSR_IDevID ident cert iak)) (pubToPrivKey iak) ;;
... ;; MakePair (TCG_CSR_IDevID ident cert iak) 
                (signature (hash (TCG_CSR_IDevID ident cert iak)) (pubToPrivKey iak)) ;; ...
*)
Fixpoint isSuperseqOfSteps1to4_OEM (seq : sequence) (ident : identifier) (cert : signedCert) (iak : pubKey) : Prop :=
  match seq with
  | c ;; s => 
      match c with
      | MakeCSR_IDevID id crt k => 
          if (decEq ident id)
          then (
            if (decEq cert crt)
            then (
              if (decEq iak k)
              then isSuperseqOfSteps2to4_OEM s (TCG_CSR_IDevID id crt k) iak
              else isSuperseqOfSteps1to4_OEM s ident cert iak )
            else isSuperseqOfSteps1to4_OEM s ident cert iak )
          else isSuperseqOfSteps1to4_OEM s ident cert iak 
      | _ => isSuperseqOfSteps1to4_OEM s ident cert iak 
      end
  | Done => False
  end.

Lemma isSuperseqOfSteps1to4_OEM_lemma : forall s iniTPM ini finTPM fin ident cert iak,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (pair (TCG_CSR_IDevID ident cert iak)
           (signature (hash (TCG_CSR_IDevID ident cert iak)) (pubToPrivKey iak))) fin ->
  ~ (In (pair (TCG_CSR_IDevID ident cert iak) 
              (signature (hash (TCG_CSR_IDevID ident cert iak)) (pubToPrivKey iak))) ini) ->
  ~ (In (signature (hash (TCG_CSR_IDevID ident cert iak)) (pubToPrivKey iak)) ini) ->
  ~ (In (hash (TCG_CSR_IDevID ident cert iak)) ini) ->
  ~ (In (hash (TCG_CSR_IDevID ident cert iak)) iniTPM) ->
  ~ (In (TCG_CSR_IDevID ident cert iak) ini) ->
  isSuperseqOfSteps1to4_OEM s ident cert iak.
Proof.
  induction s; intros iniTPM ini finTPM fin ident cert iak E I N0 N1 N2 N2_TPM N3.
  - destruct c; simpl in *; inversion E; inversion H2; 
    subst; try (eapply IHs; fdeq).
    destruct (decEq ident i);
    destruct (decEq cert s0);
    destruct (decEq iak p);
    subst; try eapply IHs; try eapply isSuperseqOfSteps2to4_OEM_lemma; fdeq.
  - inversion E; subst; congruence.
Qed.



Fixpoint isSuperseqOfStep7_OEM (seq : sequence) (ek iak : pubKey) (rand : randType) :=
  match seq with
  | c ;; s =>
      match c with
      | TPM2_ActivateCredential crd k' k0' =>
          match crd with
          | encryptedCredential n g k =>
              match n with
              | hash m =>
                  match m with
                  | publicKey k0 =>
                      if (decEq rand g)
                      then (
                        if (decEq ek k)
                        then (
                          if (decEq iak k0)
                          then (
                            if (decEq (pubToPrivKey ek) k')
                            then (
                              if (decEq (pubToPrivKey iak) k0')
                              then True
                              else isSuperseqOfStep7_OEM s ek iak rand )
                            else isSuperseqOfStep7_OEM s ek iak rand )
                          else isSuperseqOfStep7_OEM s ek iak rand )
                        else isSuperseqOfStep7_OEM s ek iak rand )
                      else isSuperseqOfStep7_OEM s ek iak rand 
                  | _ => isSuperseqOfStep7_OEM s ek iak rand
                  end
              | _ => isSuperseqOfStep7_OEM s ek iak rand
              end
          | _ => isSuperseqOfStep7_OEM s ek iak rand
          end
      | _ => isSuperseqOfStep7_OEM s ek iak rand
      end
  | Done => False
  end.







Module Type IAK_Cert_Protocol.


(* OEM parameters *)
  Parameter pubIAK : pubKey.
  Parameter pubEK : pubKey.
  Parameter certEK : signedCert.
  Parameter devInfo : deviceInfoType.

(* CA parameters *)
  Parameter pubCA : pubKey.
  Parameter pubTM : pubKey.
  Parameter nonce : randType.

(* All keys must be distinct *)
  Axiom keys_distinct :
    pubIAK <> pubEK /\
    pubIAK <> pubCA /\
    pubIAK <> pubTM /\
    pubEK <> pubCA /\
    pubEK <> pubTM /\
    pubCA <> pubTM.

  Definition privIAK := pubToPrivKey pubIAK.
  Definition privEK := pubToPrivKey pubEK.
  Definition privCA := pubToPrivKey pubCA.



(* Correct protocol first steps of OEM *)
  Definition steps1to4_OEM : sequence :=
    MakeCSR_IDevID (Device_info devInfo) certEK pubIAK ;;
    TPM2_Hash (TCG_CSR_IDevID (Device_info devInfo) certEK pubIAK) ;;
    TPM2_Sign (hash (TCG_CSR_IDevID (Device_info devInfo) certEK pubIAK)) privIAK ;;
    MakePair (TCG_CSR_IDevID (Device_info devInfo) certEK pubIAK)
             (signature (hash (TCG_CSR_IDevID (Device_info devInfo) certEK pubIAK)) privIAK) ;;
    Done.




(* The CA is trusted to know have a good initial state *)
  Definition iniTPM_CA : tpm_state :=
  [ privateKey privCA ;
    publicKey pubCA ].

  Definition ini_CA : state :=
  [ publicKey pubTM ;
    privateKey privCA ;
    publicKey pubCA ].

  Axiom CA_keys_good :
    caKey pubCA /\
    caKey pubTM.

(* Protocol steps of CA *)
(* The CA waits to recieve a message from the OEM. *)
(* That message must be in a specific form to be considered a proper request. *)
(* The CA will then execute its protocol steps on the input message. *)
(* If the protocol succeeds the CA will issue a challenge [encryptedCredential (hash (publicKey k)) nonce k0] to the OEM. *)
  Definition steps_CA (msg : message) (ident : identifier) (ek iak : pubKey) (cert : signedCert) : Prop :=
    match msg with
    | (pair (TCG_CSR_IDevID (Device_info id) (Cert k0 id0 k_ca') k) (signature m k')) =>
          ident = (Device_info id) /\ ek = k0 /\ iak = k /\ cert = (Cert k0 id0 k_ca') /\
          seq_execute (iniTPM_CA, inferFrom msg ++ ini_CA)
                      (CheckHash 
                          m 
                          (TCG_CSR_IDevID (Device_info id) (Cert k0 id0 k_ca') k) ;;
                      CheckSig 
                          (signature m k') 
                          k ;;
                      CheckCert 
                          (Cert k0 id0 k_ca') 
                          pubTM ;;
                      CheckAttributes 
                          k 
                          Restricting Signing NonDecrypting Fixing ;;
                      TPM2_Hash 
                          (publicKey k);;
                      TPM2_MakeCredential 
                          (hash (publicKey k))
                          nonce
                          k0 ;;
                      Done)
                     (hash (publicKey k) :: iniTPM_CA, 
                        encryptedCredential (hash (publicKey k)) nonce k0 :: hash (publicKey k) :: inferFrom msg ++ ini_CA)
    | _ => False
    end.


(* Correct protocol second steps of OEM *)
(* OEM waits to recieve challenge from the CA *)
Definition step7_OEM (msg : message) : sequence :=
  TPM2_ActivateCredential msg privEK privIAK ;;
  Done.



(* Candidate minimal initial state of OEM *)
  Definition iniTPM_OEM : tpm_state :=
  [ privateKey privIAK ;
    privateKey privEK ].

  Definition ini_OEM : state :=
  [ signedCertificate certEK ;
    publicKey pubIAK ].


  Lemma ini_OEM_lowerBound : forall iniTPM ini midTPM mid fin,
    seq_execute (iniTPM, ini) steps1to4_OEM (midTPM, mid) ->
    seq_execute (midTPM, inferFrom (encryptedCredential (hash (publicKey pubIAK)) nonce pubEK) ++ mid) 
                (step7_OEM (encryptedCredential (hash (publicKey pubIAK)) nonce pubEK))
                fin ->
    (iniTPM_OEM \subsetOf iniTPM) /\
    (ini_OEM \subsetOf ini).
  Proof.
    intros iniTPM ini midTPM mid fin E1 E2.
(* split steps_Owner into its individual commands *)
    inversion E1 as [initial mid0 final command steps_Owner' H_MakeCSR E10| ]; subst;
    inversion E10 as [initial mid1 final command steps_Owner' H_Hash E11| ]; subst;
    inversion E11 as [initial mid2 final command steps_Owner' H_Sign E12| ]; subst;
    inversion E12 as [initial mid3 final command steps_Owner' H_MakePair E13| ]; subst;
    inversion E13; subst;
(* Invert each individual step in reverse order *)
    inversion H_MakePair; subst; 
    inversion H_Sign; subst;
    inversion H_Hash; subst;
    inversion H_MakeCSR; subst;
    clear E1 E10 E11 E12 E13;
    clear H_MakeCSR H_Hash H_Sign H_MakePair;
    inversion E2 as [initial mid0 final command steps_Owner' H_ActivateCredential E20| ]; subst;
    inversion E20; subst;
    inversion H_ActivateCredential; subst;
    clear E2 E20;
    clear H_ActivateCredential;
    split.
    - unfold iniTPM_OEM; intros m I; inversion I; subst.
    -- rewrite <- H14. inversion H17 as [EQ_false | H17']; subst.
        inversion EQ_false.
        assumption.
    -- inversion H; subst. rewrite <- H12. inversion H16 as [EQ_false | H16']; subst.
        inversion EQ_false.
        assumption.
        inversion H1.
    - unfold ini_OEM; intros m I; inversion I; subst.
    -- assumption.
    -- inversion H; subst. assumption.
       inversion H1.
    - unfold iniTPM_OEM; intros m I; inversion I; subst.
    -- rewrite <- H14. inversion H17 as [EQ_false | H17']; subst.
        inversion EQ_false.
        assumption.
    -- inversion H; subst. rewrite <- H12. inversion H16 as [EQ_false | H16']; subst.
        inversion EQ_false.
        assumption.
        inversion H1.
    - unfold ini_OEM; intros m I; inversion I; subst.
    -- assumption.
    -- inversion H; subst. assumption. inversion H1.
  Qed.



  Lemma ini_OEM_sufficient : forall msg,
    endorsementKey pubEK ->
    steps_CA msg (Device_info devInfo) pubEK pubIAK certEK ->
    exists midTPM mid fin, 
    seq_execute (iniTPM_OEM, ini_OEM) steps1to4_OEM (midTPM, mid) /\
    seq_execute (midTPM, inferFrom (encryptedCredential (hash (publicKey pubIAK)) nonce pubEK) ++ mid) 
                (step7_OEM (encryptedCredential (hash (publicKey pubIAK)) nonce pubEK)) fin.
  Proof.
    intros m goodEK CA.
    unfold iniTPM_OEM, ini_OEM, steps1to4_OEM, step7_OEM, privEK, privIAK.
    destruct pubEK, r, s, d, f; simpl in goodEK; try inversion goodEK.
    destruct m; try inversion CA;
    destruct m1; try inversion CA;
    destruct i; try inversion CA;
    destruct s; try inversion CA;
    destruct m2; try inversion CA; subst.
    destruct H0; subst; destruct H1; subst; destruct H1; subst.
    clear CA; simpl in *.
    inversion H1 as [initial mid1 final command steps_Owner' H_CheckHash H11 | ]; subst; 
    inversion H11 as [initial mid2 final command steps_Owner' H_CheckSig H12 | ]; subst;
    inversion H12 as [initial mid3 final command steps_Owner' H_CheckCert H13 | ]; subst;
    inversion H13 as [initial mid4 final command steps_Owner' H_CheckAttributes H14 | ]; subst;
    inversion H14 as [initial mid5 final command steps_Owner' H_Hash H15 | ]; subst;
    inversion H15 as [initial mid6 final command steps_Owner' H_MakeCredential H16 | ]; subst;
    inversion H16; subst.
    inversion H_MakeCredential; subst;
    inversion H_Hash; subst;
    inversion H_CheckAttributes; subst.
    eexists. eexists. eexists. 
    split. repeat eapply SE_Seq; econstructor; simpl; auto.
    
    eapply SE_Seq. econstructor; simpl; auto.
    econstructor; simpl; auto 9. econstructor.
  Qed.



  Lemma ca_implies_isSuperseqOfSteps1to4 : forall s iniTPM ini midTPM mid msg ident ek iak cert,
    seq_execute (iniTPM, ini) s (midTPM, mid) ->
    In msg mid ->
    (forall m', needsGeneratedTPM m' -> ~ In m' iniTPM) ->
    (forall m', needsGenerated m' -> ~ In m' ini) ->
    steps_CA msg ident ek iak cert -> 
    isSuperseqOfSteps1to4_OEM s ident cert iak.
  Proof.
    intros s iniTPM ini finTPM fin m ident ek iak cert E I N_TPM N CA.
(* Get m into the form of the match statement in steps_CA *)
    destruct m; try inversion CA;
    destruct m1; try inversion CA;
    destruct i; try inversion CA;
    destruct s0; try inversion CA;
    destruct m2; try inversion CA; subst;
    destruct H0; subst; destruct H0; subst; destruct H0; subst;
    clear CA; simpl in *.
(* Split steps_CA into its individual commands *)
    inversion H0 as [initial mid1 final command steps_Owner' H_CheckHash H1 | ]; subst; 
    inversion H1 as [initial mid2 final command steps_Owner' H_CheckSig H2 | ]; subst;
    inversion H2 as [initial mid4 final command steps_Owner' H_CheckCert H3 | ]; subst;
    inversion H3 as [initial mid5 final command steps_Owner' H_CheckAttributes H4 | ]; subst;
    inversion H4; subst;
(* Invert each individual step in reverse order *) 
    inversion H_CheckAttributes; subst;
    inversion H_CheckCert; subst;
    inversion H_CheckSig; subst;
    inversion H_CheckHash; subst.
(* Apply lemma *)
    eapply isSuperseqOfSteps1to4_OEM_lemma; eauto; 
    try apply N; try apply N_TPM; simpl; trivial.
  Qed.






  
  Lemma rand_implies_isSuperseqOfStep7 : forall s2 midTPM mid finTPM fin ek iak g,  
    seq_execute (midTPM, mid) s2 (finTPM, fin) ->
    In (encryptedCredential (hash (publicKey iak)) g ek) mid ->
    (forall ki ke, iak <> ki -> ~(In (encryptedCredential (hash (publicKey ki)) g ke) mid)) ->
    (forall ki ke, ek <> ke -> ~(In (encryptedCredential (hash (publicKey ki)) g ke) mid)) ->
    ~ (In (randomNum g)) mid ->
    In (randomNum g) fin ->
    isSuperseqOfStep7_OEM s2 ek iak g.
  Proof.
    induction s2; intros midTPM mid finTPM fin ek iak g E Im N_IAK N_EK N I.
    - destruct c; simpl in *; inversion E; inversion H2;
      subst; try (eapply IHs2; fdeq);
      try (eapply IHs2; 
      [ eauto 
      | simpl 
      | intros ki ke Neq HC; inversion HC; try inversion H; try congruence; destruct (N_IAK ki ke); assumption
      | intros ki ke Neq HC; inversion HC; try inversion H; try congruence; destruct (N_EK ki ke); assumption
      | fdeq |  ]; eauto).
      destruct n; inversion H14.
      destruct (decEq g g0);
      destruct (decEq ek (Public i r s0 d f));
      destruct (decEq iak (Public i0 r0 s1 d0 f0));
      destruct (decEq (pubToPrivKey ek) (Private i r s0 d f));
      destruct (decEq (pubToPrivKey iak) (Private i0 r0 s1 d0 f0)); subst; trivial;
      eapply IHs2; eauto; try (simpl; eauto; fail); 
      try (intros ki ke Neq HC; inversion HC; try inversion H; destruct (N_IAK ki ke); assumption); 
      try (intros ki ke Neq HC; inversion HC; try inversion H; destruct (N_EK ki ke); assumption);
      try (destruct (N_IAK (Public i0 r0 s1 d0 f0) (Public i r s0 d f)); assumption);
      try (destruct (N_EK (Public i0 r0 s1 d0 f0) (Public i r s0 d f)); assumption);
      try (intros HC; inversion HC; congruence).
    - inversion E; subst; congruence.
  Qed.

  



  Lemma ca_and_rand_implies_isSuperseqOfStep7 : forall s2 s1 iniTPM ini midTPM mid finTPM fin msg ident ek iak cert g,
    seq_execute (iniTPM, ini) s1 (midTPM, mid) -> 
    In msg mid ->
    (forall m', needsGeneratedTPM m' -> ~ In m' iniTPM) ->
    (forall m', needsGenerated m' -> ~ In m' ini) ->
    steps_CA msg ident ek iak cert ->
    seq_execute (midTPM, inferFrom (encryptedCredential (hash (publicKey iak)) g ek) ++ mid) 
                 s2 
                (finTPM, fin) ->
    In (randomNum g) fin ->
    isSuperseqOfStep7_OEM s2 ek iak g.
  Proof.
    intros s2 s1 iniTPM ini midTPM mid finTPM fin m ident ek iak cert g.
    intros E1 Im N_TPM N CA E2 Ig.

    destruct m; try inversion CA;
    destruct m1; try inversion CA;
    destruct i; try inversion CA;
    destruct s; try inversion CA;
    destruct m2; try inversion CA; subst;
    destruct H0; subst; destruct H0; subst; destruct H0; subst;
    clear CA; simpl in *.

    inversion H0 as [initial mid1 final command steps_Owner' H_CheckHash H1 | ]; subst; 
    inversion H1 as [initial mid2 final command steps_Owner' H_CheckSig H2 | ]; subst;
    inversion H2 as [initial mid4 final command steps_Owner' H_CheckCert H3 | ]; subst;
    inversion H3 as [initial mid5 final command steps_Owner' H_CheckAttributes H4 | ]; subst;
    inversion H4; subst.

    inversion H_CheckAttributes; subst;
    inversion H_CheckCert; subst;
    inversion H_CheckSig; subst;
    inversion H_CheckHash; subst.

    eapply rand_implies_isSuperseqOfStep7. eauto.
    simpl; eauto.

    intros ki ke Neq HC. inversion HC; subst. inversion H. congruence.
    assert (contra : ~ In (encryptedCredential (hash (publicKey ki)) g ke) mid).
    eapply seq_exec_cannotGenerateCred_contrapositive; eauto. 
    intros n k HCC; destruct (N (encryptedCredential n g k)); simpl; trivial.
    intros HCC; destruct (N (randomNum g)); simpl; trivial.
    congruence.

    intros ki ke Neq HC. inversion HC; subst. inversion H. congruence.
    assert (contra : ~ In (encryptedCredential (hash (publicKey ki)) g ke) mid).
    eapply seq_exec_cannotGenerateCred_contrapositive; eauto. 
    intros n k HCC; destruct (N (encryptedCredential n g k)); simpl; trivial.
    intros HCC; destruct (N (randomNum g)); simpl; trivial.
    congruence.

    intros HC. inversion HC; try inversion H. clear HC. generalize dependent H.
    eapply seq_exec_cannotGenerateRand_contrapositive; eauto.
    intros HC; destruct (N (randomNum g)); simpl; trivial.
    intros n k HC; destruct (N (encryptedCredential n g k)); simpl; trivial.

    assumption.
  Qed.


  Lemma isSuperseqOfStep7_implies_activatecredential : forall s2 ek iak g,
    isSuperseqOfStep7_OEM s2 ek iak g ->
    command_in_sequence (TPM2_ActivateCredential (encryptedCredential (hash (publicKey iak)) g ek) 
                                                (pubToPrivKey ek) 
                                                (pubToPrivKey iak))
                        s2.
  Proof.
    induction s2; intros ek iak g H0; simpl.
    - destruct (decEq 
                  (TPM2_ActivateCredential (encryptedCredential (hash (publicKey iak)) g ek)
                                           (pubToPrivKey ek) 
                                           (pubToPrivKey iak)) 
                   c);
      [ trivial
      | apply IHs2; simpl in *;
        destruct c; try assumption;
        destruct m; subst; try assumption; 
        destruct m; subst; try assumption; 
        destruct m; subst; try assumption;        
        destruct (decEq g r);
        destruct (decEq ek p1);
        destruct (decEq iak p2);
        destruct (decEq (pubToPrivKey ek) p);
        destruct (decEq (pubToPrivKey iak) p0); 
        subst; congruence ].
    - inversion H0.
  Qed.


  Lemma activatecredential_implies_iakInTPM : forall s2 midTPM mid finTPM fin ek iak g,
    seq_execute (midTPM, mid) s2 (finTPM, fin) -> 
    command_in_sequence (TPM2_ActivateCredential (encryptedCredential (hash (publicKey iak)) g ek) 
                                               (pubToPrivKey ek) 
                                               (pubToPrivKey iak))
                        s2 ->
    In (privateKey (pubToPrivKey iak)) midTPM.
  Proof.
    induction s2; intros midTPM mid finTPM fin ek iak g E CI.
    - simpl in *;
      destruct (decEq 
                  (TPM2_ActivateCredential (encryptedCredential (hash (publicKey iak)) g ek)
                                           (pubToPrivKey ek) 
                                           (pubToPrivKey iak)) 
                   c);
      inversion E; subst.
    -- inversion H2; assumption.
    -- destruct mid0 as [midTPM0 mid0]; eapply exec_cannotGenerateKey; eauto.
    - inversion CI.
  Qed.


  Lemma activatecredential_implies_ekInTPM : forall s2 midTPM mid finTPM fin ek iak g,
    seq_execute (midTPM, mid) s2 (finTPM, fin) -> 
    command_in_sequence (TPM2_ActivateCredential (encryptedCredential (hash (publicKey iak)) g ek) 
                                               (pubToPrivKey ek) 
                                               (pubToPrivKey iak)) 
                      s2->
    In (privateKey (pubToPrivKey ek)) midTPM.
  Proof.
    induction s2; intros midTPM mid finTPM fin ek iak g E CI.
    - simpl in *;
      destruct (decEq 
                  (TPM2_ActivateCredential (encryptedCredential (hash (publicKey iak)) g ek)
                                           (pubToPrivKey ek) 
                                           (pubToPrivKey iak)) 
                  c);
      inversion E; subst.
    -- inversion H2; assumption.
    -- destruct mid0 as [midTPM0 mid0]; eapply exec_cannotGenerateKey; eauto.
    - inversion CI.
  Qed.


(* PROTOCOL ASSURANCES *)
(* Given the following assumptions: 
      The OEM executes some sequence of steps
      resulting in a message in its intermediate final state
      when only keys and certificates may be in its initial states.
      The CA's protocol executes successfully on the given message.
      The OEM executes some other sequence of steps upon receiving the CA's challenge
      resulting in the nonce in its final state.
*)

(* Conclude:
      The private EK and private IAK reside in the same TPM *)
  Theorem iak_and_ek_in_TPM : forall s2 s1 iniTPM ini midTPM mid finTPM fin msg ident ek iak cert g,
    seq_execute (iniTPM, ini) s1 (midTPM, mid) -> 
    In msg mid ->
    (forall m', needsGeneratedTPM m' -> ~ In m' iniTPM) ->
    (forall m', needsGenerated m' -> ~ In m' ini) ->
    steps_CA msg ident ek iak cert ->
    seq_execute (midTPM, inferFrom (encryptedCredential (hash (publicKey iak)) g ek) ++ mid) 
                 s2 
                (finTPM, fin) ->
    In (randomNum g) fin ->
    In (privateKey (pubToPrivKey iak)) iniTPM /\ In (privateKey (pubToPrivKey ek)) iniTPM.
  Proof.
    intros s2 s1 iniTPM ini midTPM mid finTPM fin m ident ek iak cert g;
    intros E1 Im N_TPM N CA E2 Ig;
    split; eapply seq_exec_cannotGenerateKey; eauto; 
    [ eapply activatecredential_implies_iakInTPM | eapply activatecredential_implies_ekInTPM ]; eauto;
    eapply isSuperseqOfStep7_implies_activatecredential; eapply ca_and_rand_implies_isSuperseqOfStep7 with (s1 := s1); eauto.
  Qed.


(* Conclude:
      The EK certificate is valid and signed by the TPM Manufacturer *)
  Theorem ek_certificate_valid : forall msg ident ek iak cert,
    steps_CA msg ident ek iak cert ->
    execute (iniTPM_CA, inferFrom msg ++ ini_CA) 
            (CheckCert cert pubTM) 
            (iniTPM_CA, inferFrom msg ++ ini_CA).
  Proof.
    intros m ident ek iak cert CA.

    destruct m; try inversion CA;
    destruct m1; try inversion CA;
    destruct i; try inversion CA;
    destruct s; try inversion CA;
    destruct m2; try inversion CA; subst;
    destruct H0; subst; destruct H0; subst; destruct H0; subst;
    clear CA; simpl in *.

    inversion H0 as [initial mid1 final command steps_Owner' H_CheckHash H1 | ]; subst; 
    inversion H1 as [initial mid2 final command steps_Owner' H_CheckSig H2 | ]; subst;
    inversion H2 as [initial mid4 final command steps_Owner' H_CheckCert H3 | ]; subst;
    inversion H3 as [initial mid5 final command steps_Owner' H_CheckAttributes H4 | ]; subst;
    inversion H4; subst.

    inversion H_CheckAttributes; subst;
    inversion H_CheckCert; subst;
    inversion H_CheckSig; subst;
    inversion H_CheckHash; subst.

    constructor; simpl; auto.
  Qed.

(* Conclude:
      The IAK is a Restricted Signing NonDecrypting key *)
  Theorem iak_good_attributes : forall msg ident ek iak cert,
    steps_CA msg ident ek iak cert ->
    attestationKey iak.
  Proof.
    intros m ident ek iak cert CA;
    destruct m; try inversion CA;
    destruct m1; try inversion CA;
    destruct i; try inversion CA;
    destruct s; try inversion CA;
    destruct m2; try inversion CA; subst;
    destruct H0; subst; destruct H0; subst; destruct H0; subst;
    clear CA; simpl in *.
    inversion H0 as [initial mid1 final command steps_Owner' H_CheckHash H1 | ]; subst; 
    inversion H1 as [initial mid2 final command steps_Owner' H_CheckSig H2 | ]; subst;
    inversion H2 as [initial mid4 final command steps_Owner' H_CheckCert H3 | ]; subst;
    inversion H3 as [initial mid5 final command steps_Owner' H_CheckAttributes H4 | ]; subst;
    inversion H4; subst.
    inversion H_CheckAttributes; subst;
    simpl; trivial.
  Qed.

(* Prove command_in_sequence s1 (TPM2_Sign _ (pubToPrivKey iak)) to show that OEM has control of the key *)


End IAK_Cert_Protocol.



(*

Module goodIAK <: IAK_Cert_Protocol.

(* OEM parameters *)
  Definition pubNewKey : pubKey := Public 51 Restricting Signing NonDecrypting.
  Definition pubEK : pubKey := Public 50 Restricting NonSigning Decrypting.
  Definition certEK : signedCert := Cert (Public 50 Restricting NonSigning Decrypting) (TPM_info 555) (Private 0 NonRestricting Signing NonDecrypting).
  Definition devInfo : deviceInfoType := 5.

(* CA parameters *)
  Definition pubCA : pubKey := Public 1 NonRestricting Signing NonDecrypting.
  Definition privCA : privKey := Private 1 NonRestricting Signing NonDecrypting.
  Definition pubTM : pubKey := Public 0 NonRestricting Signing NonDecrypting.
  Definition g : randType := 11.



  Theorem keys_distinct :
    pubNewKey <> pubEK /\
    pubNewKey <> pubCA /\
    pubNewKey <> pubTM /\
    pubEK <> pubCA /\
    pubEK <> pubTM /\
    pubCA <> pubTM.
  Proof.
    repeat split; intros contra; inversion contra.
  Qed.


Definition privIAK := pubToPrivKey pubNewKey.
Definition privEK := pubToPrivKey pubEK.


Definition min_iniTPM_OEM : tpm_state :=
[ privateKey privIAK ].

Definition min_ini_OEM : state :=
[ publicKey pubNewKey ;
  signedCertificate certEK ].



Definition steps1_OEM : sequence :=
  MakeCSR_IDevID (Device_info devInfo) certEK pubNewKey ;;
  TPM2_Hash (TCG_CSR_IDevID (Device_info devInfo) certEK pubNewKey) ;;
  TPM2_Sign (hash (TCG_CSR_IDevID (Device_info devInfo) certEK pubNewKey)) privIAK ;;
  MakePair (TCG_CSR_IDevID (Device_info devInfo) certEK pubNewKey)
           (signature (hash (TCG_CSR_IDevID (Device_info devInfo) certEK pubNewKey)) privIAK) ;;
  Done.


Theorem steps1_lowerBound : forall iniTPM ini fin,
  seq_execute (iniTPM, ini) steps1_OEM fin ->
  (min_iniTPM_OEM \subsetOf iniTPM) /\
  (min_ini_OEM \subsetOf ini).
Proof.
  intros iniTPM ini fin E.

  inversion E as [initial mid1 final command steps_Owner' H_MakeCSR E0| ]; subst. 
  inversion E0 as [initial mid2 final command steps_Owner' H_Hash E1| ]; subst.
  inversion E1 as [initial mid3 final command steps_Owner' H_Sign E2| ]; subst.
  inversion E2 as [initial mid4 final command steps_Owner' H_MakePair E3| ]; subst.
  inversion E2; subst.
  inversion E_MakePair; subst; 
  inversion E_Sign; subst;
  inversion E_Hash; subst;
  inversion E_MakeCSR; subst;
  clear E E' E'' E''' E'''';
  clear E_MakeCSR E_Hash E_Sign E_MakePair;
  split.

  - unfold min_iniTPM_OEM; intros m I; inversion I; subst.
  -- unfold privIAK; simpl ; inversion H3 as [EQ_false | H3']; subst.
      inversion EQ_false.
      assumption.
  -- inversion H; subst.

  - unfold min_ini_OEM; intros m I; inversion I; subst.
  -- assumption.
  -- inversion H; subst.
  --- assumption.
  --- inversion H0.
Qed.




Theorem steps1_min : exists fin,
  seq_execute (min_iniTPM_OEM, min_ini_OEM) steps1_OEM fin.
Proof.
  eexists; unfold min_iniTPM_OEM; unfold min_ini_OEM; unfold steps1_OEM;
  unfold privIAK; unfold privEK; unfold certEK;
  unfold pubNewKey; unfold pubEK.
  repeat eapply E_Seq; constructor; simpl; auto.
Qed.



Definition iniTPM_CA : tpm_state :=
  [ privateKey privCA ;
    publicKey pubCA ].

  Definition ini_CA : state :=
  [ publicKey pubTM ;
    privateKey privCA ;
    publicKey pubCA ].

  Theorem CA_keys_good :
    privCA = pubToPrivKey pubCA /\
    caKey pubCA /\
    caKey pubTM.
  Proof.
    repeat split.
  Qed.



  Definition steps_CA (m : message) : Prop :=
    match m with
    | ((TCG_CSR_IDevID (Device_info id) (Cert k_EK id0 k_ca') k),,
       (signature m k')) =>
          seq_execute (iniTPM_CA, inferFrom m ++ ini_CA)
                            (CheckHash m 
                                      (TCG_CSR_IDevID (Device_info id) (Cert k_EK id0 k_ca') k) ;;
                            CheckSig (signature m k') k ;;
                            CheckCert (Cert k_EK id0 k_ca') pubTM ;;
                            CheckAttributes k Restricting Signing NonDecrypting ;;
                            TPM2_Hash (publicKey k) ;;
                            TPM2_MakeCredential (hash (publicKey k)) g k_EK ;;
                            Done)
                            (iniTPM_CA, 
                             inferFrom m ++ ini_CA)
    | _ => False
    end.


(* Correct protocol second steps of OEM *)
(* OEM waits to recieve challenge from the CA *)
  Definition steps2_OEM (m : message) : sequence :=
    TPM2_ActivateCredential m privEK privIAK ;;
    Done.

End goodIAK.

*)
