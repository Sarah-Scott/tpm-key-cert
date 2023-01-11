
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Import ListNotations.



(* Keys *)
(* **** *)

Definition key_id := nat.

Inductive restrict_att : Type :=
| Restricted
| NonRestricted.

Inductive sign_att : Type :=
| Signing
| NonSigning.

Inductive decrypt_att : Type :=
| Decrypting
| NonDecrypting.


Inductive pubKey : Type :=
| Public : key_id -> restrict_att -> sign_att -> decrypt_att -> pubKey.

Inductive privKey : Type :=
| Private : key_id -> restrict_att -> sign_att -> decrypt_att -> privKey.


Definition pubtoPrivKey (k : pubKey) : privKey :=
  match k with
  | Public i r s d => Private i r s d
  end.

Definition privToPubKey (k : privKey) : pubKey :=
  match k with
  | Private i r s d => Public i r s d
  end.


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

(* currently unused *)
Inductive entity : Set :=
| tm
| oem
| owner.




(* Small-Step Semantics *)
(* ******************** *)

Definition randType := nat.

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
| Sequence : command -> command -> command.

(* corresponds to what an entity knows *)
Definition state := list message. (* not necessarily exhaustive *)

(* contains everything produced by a TPM command *)
Definition tpm_state := list message. (* subset of state *)



Notation "m1 ,, m2" := (pair m1 m2)  (at level 90, left associativity).
Notation "c1 ;; c2" := (Sequence c1 c2) (at level 90, left associativity).


Inductive execute : tpm_state * state -> command -> tpm_state * state -> Prop :=
| E_CheckAttributes : forall stTPM st i r s d,
    execute (stTPM, st)
            (CheckAttributes (Public i r s d) r s d)  (* all key attributes match input *)
            (stTPM,
             st)

| E_GetRandom : forall stTPM st g,
    execute (stTPM, st)
            (TPM2_GetRandom g) 
            (rand g :: stTPM,
             rand g :: st)

| E_CheckNonce : forall stTPM st g,
    In (rand g) stTPM ->            (* golden value secret resides in TPM *)
    execute (stTPM, st)
            (CheckNonce (rand g) g) (* input matches golden value *)
            (stTPM,
             st)

| E_Hash : forall stTPM st m,
    In m st ->                      (* message to be hashed *)
    execute (stTPM, st)
            (TPM2_Hash m)
            (hash m :: stTPM,
             hash m :: st)

| E_CheckHash : forall stTPM st m,
    In (hash m) st ->               (* hash digest *)
    In m st ->                      (* message to check against hash *)
    execute (stTPM, st)
            (CheckHash (hash m) m)  (* hash of message matches digest *)
            (stTPM,
             st)

| E_SignR : forall stTPM st m i d,                            (* must use Restricted Signing key *)
    In (privateKey (Private i Restricted Signing d)) stTPM -> (* key resides in TPM *)
    In m stTPM ->                                   (* message to be signed resides in same TPM *)
    execute (stTPM,st)
            (TPM2_Sign m (Private i Restricted Signing d))
            (sign m (Private i Restricted Signing d) :: stTPM,
             sign m (Private i Restricted Signing d) :: st)

| E_SignNR : forall stTPM st m i d,                               (* must use NonRestricted Signing key *)
    In (privateKey (Private i NonRestricted Signing d)) stTPM ->  (* key resides in TPM *)
    In m st ->                                                    (* message to be signed *)
    execute (stTPM, st)
            (TPM2_Sign m (Private i NonRestricted Signing d))
            (sign m (Private i NonRestricted Signing d) :: stTPM,
             sign m (Private i NonRestricted Signing d) :: st)

| E_CheckSig : forall stTPM st m i r s d,
    In (sign m (Private i r s d)) st ->   (* signature *)
    In (publicKey (Public i r s d)) st -> (* public part of key that performed the signature *)
    execute (stTPM, st)
            (CheckSig (sign m (Private i r s d)) (Public i r s d)) (* key id and attributes must be identical *)
            (stTPM,
             st)

| E_Certify : forall stTPM st i r s d i0 r0 d0,
    In (privateKey (Private i r s d)) stTPM ->   (* private part of key to be certified resides in TPM *)
    In (privateKey (Private i0 r0 Signing d0)) stTPM ->  (* key to sign the TPM2_Attest structure resides in same TPM *)
    execute (stTPM, st)
            (TPM2_Certify (Public i r s d) (Private i0 r0 Signing d0))
            (sign (TPM2B_Attest (Public i r s d)) (Private i0 r0 Signing d0) :: stTPM,
             sign (TPM2B_Attest (Public i r s d)) (Private i0 r0 Signing d0) :: st)

| E_MakeCredential : forall stTPM st m g i r s,
    In m st ->                    (* hash of public part of key i.e., name of key *)
    In (rand g) stTPM ->          (* secret resides in TPM *)
    In (publicKey (Public i r s Decrypting)) st ->  (* key to encrypt the credential structure *)
    execute (stTPM, st)
            (TPM2_MakeCredential m g (Public i r s Decrypting)) 
            (encrypt (credential m g) (Public i r s Decrypting) :: stTPM,
             encrypt (credential m g) (Public i r s Decrypting) :: st)

| E_ActivateCredential : forall stTPM st m g i r s i0 r0 s0 d0,
    In (encrypt (credential (hash m) g) (Public i r s Decrypting)) st -> (* encrypted credential structure *)
    In (privateKey (Private i r s Decrypting)) stTPM ->  (* key to decrypt resides in TPM *)
    In (privateKey (Private i0 r0 s0 d0)) stTPM -> (* private part of key to be certified resides in same TPM *)
    execute (stTPM,
             hash m :: st)
            (CheckHash (hash m) (publicKey (Public i0 r0 s0 d0))) (* name in credential structure matches key to be certified*)
            (stTPM,
             hash m :: st) ->
    execute (stTPM, st)
            (TPM2_ActivateCredential (encrypt (credential (hash m) g) (Public i r s Decrypting)) 
                                     (Private i r s Decrypting)
                                     (Private i0 r0 s0 d0)) 
            (rand g :: credential (hash m) g :: stTPM,
             rand g :: credential (hash m) g :: st)
             
| E_MakeCSR_IDevID : forall stTPM st m i r s d,
    In m st ->                            (* EK certificate *)
    In (publicKey (Public i r s d)) st -> (* public part of IAK *)
    execute (stTPM, st)
            (MakeCSR_IDevID m (Public i r s d))
            (stTPM,
             TCG_CSR_IDevID m (Public i r s d) :: st)

| E_MakeCSR_LDevID : forall stTPM st m1 m2,
    In m1 stTPM ->    (* signed TPM2_Attest structure resides in TPM *)
    In m2 st ->       (* IAK certificate *)
    execute (stTPM, st)
            (MakeCSR_LDevID m1 m2)
            (stTPM,
             TCG_CSR_LDevID m1 m2 :: st)

| E_MakeCert : forall stTPM st i r s d i0 d0,
    In (publicKey (Public i r s d)) st ->                           (* key to be certified *)
    In (privateKey (Private i0 NonRestricted Signing d0)) stTPM ->  (* key to sign the certificate resides in TPM *)
    execute (stTPM, st)
            (MakeCert (Public i r s d) (Private i0 NonRestricted Signing d0))
            (sign (certificate (Public i r s d)) (Private i0 NonRestricted Signing d0) :: stTPM,
             sign (certificate (Public i r s d)) (Private i0 NonRestricted Signing d0) :: st)

| E_Sequence : forall ini mid fin c1 c2,
    execute ini c1 mid ->
    execute mid c2 fin ->
    execute ini (Sequence c1 c2) fin.


(* execute is a partial function *)
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




(* Some random theorems regarding execute *)


Lemma sequence_first : forall ini c1 c2 fin,
execute ini (c1 ;; c2) fin ->
exists ini1 mid1, execute ini1 c1 mid1.
Proof.
  intros ini c1 c2 fin H; inversion H; subst.
  exists ini; exists mid; assumption.
Qed.

Lemma sequence_second : forall ini c1 c2 fin,
execute ini (c1 ;; c2) fin ->
exists ini2 mid2, execute ini2 c2 mid2.
Proof.
  intros ini c1 c2 fin H; inversion H; subst.
  exists mid; exists fin; assumption.
Qed.

Theorem sequence_split : forall ini c1 c2 fin,
execute ini (c1 ;; c2) fin ->
(exists ini1 mid1, execute ini1 c1 mid1) /\ 
(exists mid2 fin2, execute mid2 c2 fin2).
Proof.
  intros ini c1 c2 fin H; inversion H; subst.
  split.
  - exists ini; exists mid; assumption.
  - exists mid; exists fin; assumption.
Qed.


Print ex_intro.

Lemma execute_exIntro : forall ini0 c fin0,
execute ini0 c fin0 ->
exists fin, execute ini0 c fin.
Proof.
  intros ini0 c fin0 E0;
  eexists; apply E0.
Qed. 


(* failed proof *)
Theorem ini_generalize : forall stTPM0 stTPM st0 st c fin0,
execute (stTPM0, st0) c fin0 ->
incl stTPM0 stTPM ->
incl st0 st ->
exists fin, execute (stTPM, st) c fin.
Proof.
  intros stTPM0 stTPM st0 st c fin0 E0 H_TPM H.
  induction c; inversion E0; subst; eexists; execute_constructor;
  unfold incl in *;
    try (apply H_TPM; assumption);
    try (apply H; assumption).
  - inversion H9; subst; execute_constructor.
  -- apply in_eq.
  -- simpl in *; right; apply H; inversion H6 as [H6_left | ];
      [inversion H6_left | assumption].
  - (* Sequence Case *)

  Restart.

  intros stTPM0 stTPM st0 st c fin0 E0 H_TPM H.
  induction c.
  - inversion E0; subst; eexists; execute_constructor.
  - inversion E0; subst; eexists; execute_constructor.
  - inversion E0; subst; eexists; execute_constructor;
    unfold incl in *;
    try (apply H_TPM; assumption);
    try (apply H; assumption).
  - inversion E0; subst; eexists; execute_constructor;
    unfold incl in *;
    try (apply H_TPM; assumption);
    try (apply H; assumption).
  - inversion E0; subst; eexists; execute_constructor;
    unfold incl in *;
    try (apply H_TPM; assumption);
    try (apply H; assumption).
  - inversion E0; subst; eexists; execute_constructor;
    unfold incl in *;
    try (apply H_TPM; assumption);
    try (apply H; assumption).
  - inversion E0; subst; eexists; execute_constructor;
    unfold incl in *;
    try (apply H_TPM; assumption);
    try (apply H; assumption).
  - inversion E0; subst; eexists; execute_constructor;
    unfold incl in *;
    try (apply H_TPM; assumption);
    try (apply H; assumption).
  - inversion E0; subst; eexists; execute_constructor;
    unfold incl in *;
    try (apply H_TPM; assumption);
    try (apply H; assumption).
  - inversion E0; subst; eexists; execute_constructor;
    unfold incl in *;
    try (apply H_TPM; assumption);
    try (apply H; assumption).
    inversion H9; subst; execute_constructor.
    -- apply in_eq.
    -- simpl in *; right; apply H; inversion H6 as [H6_left | ];
        [inversion H6_left | assumption].
  - inversion E0; subst; eexists; execute_constructor;
    unfold incl in *;
    try (apply H_TPM; assumption);
    try (apply H; assumption).
  - inversion E0; subst; eexists; execute_constructor;
    unfold incl in *;
    try (apply H_TPM; assumption);
    try (apply H; assumption).
  - inversion E0; subst; eexists; execute_constructor;
    unfold incl in *;
    try (apply H_TPM; assumption);
    try (apply H; assumption).
  - (* Sequence Case *)
Abort.


(* Discovery *)
(* ********* *)

(* an entity who knows a message can discover additional messages from it *)
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
| D_CSR_IDevID : forall m k st,  (* contents of TCG_CSR_IDevID *)
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


(* when sending a message the recipient can discover these additional messages *)
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



Definition iniTPM : tpm_state :=
[ publicKey pubNewKey ; (* IAK public *)
  privateKey privNewKey ;   (* IAK private *)
  publicKey pubEK ;         (* EK public *)
  privateKey privEK ].           (* EK private *)

Definition ini : state :=
[ publicKey pubNewKey ;
  privateKey privNewKey ;
  certEK ;    (* EK certificate *)
  publicKey pubEK ;
  privateKey privEK ].


Definition c1 : command :=
MakeCSR_IDevID certEK pubNewKey ;; (* 1 *)
TPM2_Hash (TCG_CSR_IDevID certEK pubNewKey) ;;     (* 2 *)
TPM2_Sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey.                  (* 3 *)


Definition midTPM : state :=
sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey :: (* 3 *)
hash (TCG_CSR_IDevID certEK pubNewKey) ::                               (* 2 *)
iniTPM.

Definition mid : state :=
sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey :: (* 3 *)
hash (TCG_CSR_IDevID certEK pubNewKey) ::                               (* 2 *)
(TCG_CSR_IDevID certEK pubNewKey) ::                                    (* 1 *)
ini.


(*
send ((TCG_CSR_IDevID certEK pubNewKey),, (sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey))   (* 4 *)
*)

Definition iniTPM_CA : tpm_state :=
[ privateKey privCA ;   (* OEM CA private *)
  publicKey pubCA ]. (* OEM CA public *)

Definition ini_CA : state :=
[ publicKey pubTM ;    (* TM CA public*)
  privateKey privCA ;
  publicKey pubCA ].


Definition c1_CA : command :=
CheckHash (hash (TCG_CSR_IDevID certEK pubNewKey)) (TCG_CSR_IDevID certEK pubNewKey) ;;     (* 5a *)
CheckSig (sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey) pubNewKey ;;           (* 5b *)
CheckSig certEK pubTM ;;           (* 5c *)
CheckAttributes pubNewKey Restricted Signing NonDecrypting ;;                    (* 5d *)
TPM2_Hash (publicKey pubNewKey) ;;                              (* 6 *)
TPM2_GetRandom r ;;                                                   (* 7 *)
TPM2_MakeCredential (hash (publicKey pubNewKey)) r pubEK. (* 8 *)


Definition midTPM_CA : tpm_state :=
encrypt (credential (hash (publicKey pubNewKey)) r) pubEK ::  (* 8 *)
rand r ::                                                                 (* 7 *)
hash (publicKey pubNewKey) ::                                       (* 6 *)
iniTPM_CA.

Definition mid_CA : state :=
encrypt (credential (hash (publicKey pubNewKey)) r) pubEK ::  (* 8 *)
rand r ::                                                                 (* 7 *)
hash (publicKey pubNewKey) ::                                       (* 6 *)
send ((TCG_CSR_IDevID certEK pubNewKey),, (sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey)) ++ (* 4 *)
ini_CA.


(*
send (encrypt (credential (hash (publicKey pubNewKey)) r) pubEK)   (* 9 *)
*)

Definition c2 : command :=
TPM2_ActivateCredential (encrypt (credential (hash (publicKey pubNewKey)) r) pubEK) privEK (privNewKey).  (* 10 *)
                        

Definition finTPM : tpm_state :=
rand r ::                                            (* 10 *)
credential (hash (publicKey pubNewKey)) r ::   (* 10 *)
midTPM.

Definition fin : state :=
rand r ::                                                                        (* 10 *)
credential (hash (publicKey pubNewKey)) r  ::                               (* 10 *)
send (encrypt (credential (hash (publicKey pubNewKey)) r) pubEK) ++  (* 9 *)
mid.

(*
send (rand r)    (* 11 *)
*)

Definition c2_CA : command :=
CheckNonce (rand r) r ;;                           (* 12 *)
MakeCert pubNewKey privCA.  (* 13 *)

Definition finTPM_CA : state := 
sign (certificate pubNewKey) privCA ::  (* 13 *)
midTPM_CA.

Definition fin_CA : state := 
sign (certificate pubNewKey) privCA ::  (* 13 *)
send (rand r) ++                                               (* 11 *)
mid_CA.


(* Line A in 'Relationships of Keys/Certificates' diagram *)
Axiom CertIAK_spec :
execute (iniTPM, ini) c1 (midTPM, mid) /\     (* Steps 0 - 3 *)
In (TCG_CSR_IDevID certEK pubNewKey) mid /\ (* Step 4 *)
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

(* all failed proofs (need additional helper lemmas) *)

(* A TPM is authentic *)
(* [EK Certificate is valid] *)
Theorem authenticTPM : exists success,
execute (iniTPM_CA, certEK :: ini_CA)
        (CheckSig certEK pubTM)
         success.
Proof.
Abort.

(* This specific TPM is authentic and is represented by the EK Certificate *)
(* [EK resident in this TPM corresponds to the EK Certificate] *)
(* Theorem authenticThisTPM *)

  
(* This AK is authentic *)
(* [AK in CSR is resident in the same TPM as the EK] *)
(* authenticAK *)

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



Definition iniTPM : tpm_state :=
[ publicKey pubNewKey ; (* IAK public *)
  privateKey privNewKey ;   (* IAK private *)
  publicKey pubEK ;         (* EK public *)
  privateKey privEK ].           (* EK private *)

Definition ini : state :=
[ publicKey pubNewKey ;
  privateKey privNewKey ;
  certEK ;    (* EK certificate *)
  publicKey pubEK ;
  privateKey privEK ].


Definition c1 : command :=
MakeCSR_IDevID certEK pubNewKey ;; (* 1 *)
TPM2_Hash (TCG_CSR_IDevID certEK pubNewKey) ;;     (* 2 *)
TPM2_Sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey.                  (* 3 *)


Definition midTPM : state :=
sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey :: (* 3 *)
hash (TCG_CSR_IDevID certEK pubNewKey) ::                               (* 2 *)
iniTPM.

Definition mid : state :=
sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey :: (* 3 *)
hash (TCG_CSR_IDevID certEK pubNewKey) ::                               (* 2 *)
(TCG_CSR_IDevID certEK pubNewKey) ::                                    (* 1 *)
ini.


Local Hint Unfold mid midTPM c1 ini iniTPM : core.



Definition iniTPM_CA : tpm_state :=
[ privateKey privCA ;   (* OEM CA private *)
  publicKey pubCA ]. (* OEM CA public *)

Definition ini_CA : state :=
[ publicKey pubTM ;    (* TM CA public*)
  privateKey privCA ;
  publicKey pubCA ].


Definition c1_CA : command :=
CheckHash (hash (TCG_CSR_IDevID certEK pubNewKey)) (TCG_CSR_IDevID certEK pubNewKey) ;;                                   (* 5a *)
CheckSig (sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey)                 (* 5b *)
         (pubNewKey) ;;
CheckSig (certEK)           (* 5c *)
         (pubTM) ;;
CheckAttributes (pubNewKey) Restricted Signing NonDecrypting ;;                    (* 5d *)
TPM2_Hash (publicKey pubNewKey) ;;                              (* 6 *)
TPM2_GetRandom r ;;                                                   (* 7 *)
TPM2_MakeCredential (hash (publicKey pubNewKey)) r (pubEK). (* 8 *)


Definition midTPM_CA : tpm_state :=
encrypt (credential (hash (publicKey pubNewKey)) r) (pubEK) ::  (* 8 *)
rand r ::                                                                 (* 7 *)
hash (publicKey pubNewKey) ::                                       (* 6 *)
iniTPM_CA.

Definition mid_CA : state :=
encrypt (credential (hash (publicKey pubNewKey)) r) (pubEK) ::  (* 8 *)
rand r ::                                                                 (* 7 *)
hash (publicKey pubNewKey) ::                                       (* 6 *)
send ((TCG_CSR_IDevID certEK pubNewKey),, (sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey)) ++          (* 4 *)
ini_CA.


Local Hint Unfold mid_CA midTPM_CA c1_CA ini_CA iniTPM_CA : core.



(*
send (encrypt (credential (hash (publicKey pubNewKey)) r) pubEK)   (* 9 *)
*)

Definition c2 : command :=
TPM2_ActivateCredential (encrypt (credential (hash (publicKey pubNewKey)) r) pubEK) privEK (privNewKey).  (* 10 *)
                        

Definition finTPM : tpm_state :=
rand r ::                                            (* 10 *)
credential (hash (publicKey pubNewKey)) r ::   (* 10 *)
midTPM.

Definition fin : state :=
rand r ::                                                                        (* 10 *)
credential (hash (publicKey pubNewKey)) r  ::                               (* 10 *)
send (encrypt (credential (hash (publicKey pubNewKey)) r) pubEK) ++  (* 9 *)
mid.

Local Hint Unfold fin finTPM c2 : core.

(*
send (rand r)    (* 11 *)
*)

Definition c2_CA : command :=
CheckNonce (rand r) r ;;                           (* 12 *)
MakeCert pubNewKey privCA.  (* 13 *)

Definition finTPM_CA : state := 
sign (certificate pubNewKey) privCA ::  (* 13 *)
midTPM_CA.

Definition fin_CA : state := 
sign (certificate pubNewKey) privCA ::  (* 13 *)
send (rand r) ++                                               (* 11 *)
mid_CA.


Local Hint Unfold fin_CA finTPM_CA c2_CA : core.

(* Line A in 'Relationships of Keys/Certificates' diagram *)
Theorem CertIAK_spec :
execute (iniTPM, ini) c1 (midTPM, mid) /\
In (TCG_CSR_IDevID certEK pubNewKey) mid /\
In (sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey) mid /\ 
execute (iniTPM_CA, send ((TCG_CSR_IDevID certEK pubNewKey),, sign (hash (TCG_CSR_IDevID certEK pubNewKey)) privNewKey) ++ ini_CA)
         c1_CA
        (midTPM_CA, mid_CA) /\
In (encrypt (credential (hash (publicKey pubNewKey)) r) pubEK) mid_CA /\
execute (midTPM, send (encrypt (credential (hash (publicKey pubNewKey)) r) pubEK) ++ mid) 
         c2
        (finTPM, fin) /\
In (rand r) fin /\
execute (midTPM_CA, send (rand r) ++ mid_CA)
         c2_CA
        (finTPM_CA, fin_CA).
Proof.
  repeat split; autounfold; repeat execute_constructor; simpl; auto 11.
Qed.



End myIAK. 

