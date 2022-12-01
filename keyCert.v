
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Import ListNotations.

Section KeyCert.

(* Keys *)
(* **** *)

(* TODO: TPM and Device identities/info *)

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
| DevID : ak_val -> key_val (* device identification key *)
| CA : ca_val -> key_val    (* certificate authority key *)
| Bad : key_val.

Inductive keyType : Type :=
| Private : key_val -> keyType
| Public : key_val -> keyType.

Inductive Restricted : key_val -> Prop :=
| R_EK : Restricted EK
| R_AK : forall a, Restricted (AK a).

Inductive NonRestricted : key_val -> Prop :=
| NR_DevID : forall a, NonRestricted (DevID a) 
| NR_CA : forall c, NonRestricted (CA c)
| NR_Bad : NonRestricted Bad.

Inductive Signing : key_val -> Prop :=
| S_AK : forall a, Signing (AK a)
| S_DevID : forall a, Signing (DevID a)
| S_CA : forall c, Signing (CA c)
| S_Bad : Signing Bad.

Inductive Decrypting : key_val -> Prop :=
| D_EK : Decrypting EK
| D_Bad : Decrypting Bad.

Hint Constructors Restricted NonRestricted Signing Decrypting : core.

Theorem or_RestrictedNonRestricted : forall v,
Restricted v \/ NonRestricted v.
Proof.
  intros v; destruct v; auto.
Qed.

Theorem or_SigningDecrypting : forall v,
Signing v \/ Decrypting v.
Proof.
  intros v; destruct v; auto.
Qed.

Hint Resolve or_RestrictedNonRestricted or_SigningDecrypting : core.




(* Small-Step Semantics *)
(* ******************** *)

Definition randType := nat.

Inductive message : Type :=
| key : keyType -> message
| rand : randType -> message
| TPM2B_Attest : keyType -> message
| hash : message -> message
| sign : message -> keyType -> message
| credential : message -> randType -> message
| encrypt : message -> keyType -> message
| TCG_CSR_LDevID : message -> message -> message
| TCG_CSR_IDevID : message -> message -> message
| certificate : keyType -> message    (* TODO: keyType -> id -> message *)
| pair : message -> message -> message.

Inductive command : Type :=
| TPM2_Certify : keyType -> keyType -> command
| MakeCSR_LDevID : message -> message -> command
| MakeCSR_IDevID : message -> keyType -> command (* TODO: id -> message -> keyType -> command*)
| TPM2_Hash : message -> command
| CheckHash : message -> message -> command
| TPM2_Sign : message -> keyType -> command
| CheckSig : message -> keyType -> command
| TPM2_GetRandom : randType -> command
| CheckNonce : message -> randType -> command
| TPM2_MakeCredential : message -> randType -> keyType -> command
| TPM2_ActivateCredential : message -> keyType -> keyType -> command
| MakeCert : keyType -> keyType -> command  (* TODO: keyType -> id -> keyType -> message *)
| Sequence : command -> command -> command.

(* corresponds to what an entity knows *)
Definition tpm_state := list message. (* subset of state *)
Definition state := list message.

Notation "m1 ,, m2" := (pair m1 m2)  (at level 90, left associativity).
Notation "c1 ;; c2" := (Sequence c1 c2) (at level 90, left associativity).


Inductive execute : tpm_state * state -> command -> tpm_state * state -> Prop :=
| E_Certify : forall stTpm st v v0,
    In (key (Private v)) stTpm ->   (* private part of key to be certified resides in TPM *)
    In (key (Private v0)) stTpm ->  (* key to sign the TPM2_Attest structure resides in same TPM *)
    Signing v0 ->
    execute (stTpm, st)
            (TPM2_Certify (Public v) (Private v0)) 
            (((sign (TPM2B_Attest (Public v)) (Private v0))::stTpm),
             ((sign (TPM2B_Attest (Public v)) (Private v0))::st))
| E_MakeCSR_LDevID : forall stTpm st m1 m2,
    In m1 stTpm ->    (* signed TPM2_Attest structure resides in TPM *)
    In m2 st ->       (* IAK certificate *)
    execute (stTpm, st)
            (MakeCSR_LDevID m1 m2)
            (stTpm,
            ((TCG_CSR_LDevID m1 m2)::st))
| E_MakeCSR_IDevID : forall stTpm st m k,
    In m st ->        (* EK certificate *)
    In (key k) st ->  (* public part of IAK *)
    execute (stTpm, st)
            (MakeCSR_IDevID m k)
            (stTpm,
            (TCG_CSR_IDevID m (key k))::st)
| E_Hash : forall stTpm st m,
    In m st ->        (* message to be hashed *)
    execute (stTpm, st)
            (TPM2_Hash m)
            ((hash m)::stTpm,
             (hash m)::st)
| E_CheckHash : forall stTpm st m,
    In (hash m) st -> (* hash digest *)
    In m st ->        (* message to check against hash *)
    execute (stTpm, st)
            (CheckHash (hash m) m)
            (stTpm, st)
| E_SignNR : forall stTpm st m v,
    In (key (Private v)) stTpm -> (* key to sign resides in TPM *)
    Signing v ->
    NonRestricted v ->            (* key must be NonRestricted *)
    In m st ->
    execute (stTpm, st)
            (TPM2_Sign m (Private v))
            ((sign m (Private v))::stTpm,
             (sign m (Private v))::st)
| E_SignR : forall stTpm st m v,
    In (key (Private v)) stTpm -> (* key to sign resides in TPM *)
    Signing v ->
    Restricted v ->               (* ? not required ? *)
    In m stTpm ->                 (* message to be signed resides in same TPM *)
    execute (stTpm,st)
            (TPM2_Sign m (Private v))
            ((sign m (Private v))::stTpm,
             (sign m (Private v))::st)
| E_CheckSig : forall stTpm st m v,
    In (sign m (Private v)) st -> (* signature *)
    In (key (Public v)) st ->     (* public part of key that performed the signature *)
    execute (stTpm, st)
            (CheckSig (sign m (Private v)) (Public v))
            (stTpm, st)
| E_GetRandom : forall stTpm st r,
    execute (stTpm, st) 
            (TPM2_GetRandom r) 
            ((rand r)::stTpm,
             (rand r)::st)
| E_CheckNonce : forall stTpm st r,
    In (rand r) stTpm ->          (* golden value secret resides in TPM *)
    execute (stTpm, st)
            (CheckNonce (rand r) r)
            (stTpm, st)
| E_MakeCredential : forall stTpm st m r v0,
    In m st ->                    (* hash of public part of key i.e., name of key *)
    In (rand r) stTpm ->          (* secret resides in TPM *)
    In (key (Public v0)) st ->    (* key to encrypt the credential structure *)
    Decrypting v0 ->
    execute (stTpm, st)
            (TPM2_MakeCredential m r (Public v0)) 
            ((encrypt (credential m r) (Public v0))::stTpm,
             (encrypt (credential m r) (Public v0))::st)
| E_ActivateCredential : forall stTpm st m r v v0,
    In (encrypt (credential (hash m) r) (Public v)) st -> (* encrypted credential structure *)
    In (key (Private v)) stTpm ->  (* key to decrypt resides in TPM *)
    Decrypting v ->
    In (key (Private v0)) stTpm -> (* private part of key to be certified resides in same TPM *)
    execute (stTpm, (hash m)::st) (CheckHash (hash m) (key (Public v0))) (stTpm, (hash m)::st) ->
    execute (stTpm, st)
            (TPM2_ActivateCredential (encrypt (credential (hash m) r) (Public v)) 
                                     (Private v)
                                     (Private v0)) 
            ((rand r)::(credential (hash m) r)::stTpm,
             (rand r)::(credential (hash m) r)::st)
| E_MakeCert : forall stTpm st k v0,
    In (key k) st ->                (* key to be certified *)
    In (key (Private v0)) stTpm ->  (* key to sign the certificate resides in TPM *)
    Signing v0 ->
    execute (stTpm, st)
            (MakeCert k (Private v0))
            ((sign (certificate k) (Private v0))::stTpm,
             (sign (certificate k) (Private v0))::st)
| E_Sequence : forall stTpm st stTpm' st' stTpm'' st'' c1 c2,
    execute (stTpm,st) c1 (stTpm',st') ->
    execute (stTpm',st') c2 (stTpm'',st'') ->
    execute (stTpm,st) (Sequence c1 c2) (stTpm'',st'').

Hint Constructors execute : core.

Ltac execute_constructor :=
match goal with
| [ |- execute _ (TPM2_Sign _ (Private (AK _))) _ ] => apply E_SignR
| [ |- execute _ (TPM2_Sign _ (Private (DevID _))) _ ] => apply E_SignNR
| [ |- execute _ (TPM2_Sign _ (Private (CA _))) _ ] => apply E_SignNR
| [ |- execute _ (TPM2_Sign _ (Private (Bad))) _ ] => apply E_SignNR
| [ |- execute _ (Sequence _ _) _ ] => eapply E_Sequence
| [ |- execute _ _ _] => constructor
end.



(* Discovery *)
(* ********* *)

(* an entity who knows a message can discover additional messages from it *)
Inductive discoverable : message -> state -> Prop :=
| D_key : forall k,
    discoverable (key k) [key k]
| D_rand : forall r,
    discoverable (rand r) [rand r]
| D_Attest : forall k,                  (* contents of TPM2_Attest structure *)
    discoverable (TPM2B_Attest k) [(TPM2B_Attest k); (key k)] 
| D_hash : forall m,
    discoverable (hash m) [hash m]
| D_sign : forall m k st,               (* contents of signature *)
    discoverable m st ->
    discoverable (sign m k) ((sign m k)::st)
| D_credential : forall m r,
    discoverable (credential m r) [credential m r]
| D_encrypt : forall m k,
    discoverable (encrypt m k) [encrypt m k]
| D_CSR_LDevID : forall m1 m2 st1 st2,  (* contents of TCG_CSR_LDevID *)
    discoverable m1 st1 ->
    discoverable m2 st2 ->
    discoverable (TCG_CSR_LDevID m1 m2) ((TCG_CSR_LDevID m1 m2)::st1++st2)
| D_CSR_IDevID : forall m1 m2 st1 st2,  (* contents of TCG_CSR_IDevID *)
    discoverable m1 st1 -> 
    discoverable m2 st2 ->
    discoverable (TCG_CSR_IDevID m1 m2) ((TCG_CSR_IDevID m1 m2)::st1++st2)
| D_certificate : forall k,             (* contents of certificate *)
    discoverable (certificate k) [(certificate k); (key k)]
| D_pair : forall m1 m2 st1 st2,        (* contents of pair *)
    discoverable m1 st1 ->
    discoverable m2 st2 -> 
    discoverable (pair m1 m2) ((m1,,m2)::(st1++st2)).

Hint Constructors discoverable : core.

(* when sending a message the recipient can discover these additional messages *)
Fixpoint send (m : message) : state :=
match m with
  | TPM2B_Attest k => [(TPM2B_Attest k); (key k)]
  | sign m0 k => ((sign m0 k)::(send m0))
  | TCG_CSR_LDevID m1 m2 => ((TCG_CSR_LDevID m1 m2)::(send m1)++(send m2))
  | TCG_CSR_IDevID m1 m2 => ((TCG_CSR_IDevID m1 m2)::(send m1)++(send m2))
  | certificate k => [(certificate k); (key k)]
  | pair m1 m2 => ((m1,,m2)::((send m1)++(send m2)))
  | _ => [m]
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

Hint Resolve iff_DiscoverableSend : core.







(* Owner creation of LAK certificate based on IAK certificate *)
(* ********************************************************** *)

(* Numerical comment tags correspond to respective steps in latex documentation *)

Definition ownerIniTpm : tpm_state :=
[ key (Public (AK local)) ;     (* LAK public *)
  key (Private (AK local)) ;    (* LAK private *)
  key (Public (AK initial)) ;   (* IAK public *)
  key (Private (AK initial)) ]. (* IAK private *)

Definition ownerIni : state :=
[ key (Public (AK local)) ;
  key (Private (AK local)) ;
  sign (certificate (Public (AK initial))) (Private (CA oem)) ; (* IAK certificate *)
  key (Public (AK initial)) ;
  key (Private (AK initial)) ].


(* Certificate Signing Request for local attestation key *)
Definition CSR_LAK : message :=
TCG_CSR_LDevID 
  (sign (TPM2B_Attest (Public (AK local))) (Private (AK initial)))  (* signed TPM2_Attest structure *)
  (sign (certificate (Public (AK initial))) (Private (CA oem))).    (* IAK certificate *)

Definition ownerSteps : command :=
TPM2_Certify (Public (AK local)) (Private (AK initial)) ;;                      (* 1 *)
MakeCSR_LDevID (sign (TPM2B_Attest (Public (AK local))) (Private (AK initial))) (* 2 *)
               (sign (certificate (Public (AK initial))) (Private (CA oem))) ;;
TPM2_Hash CSR_LAK ;;                                                            (* 3 *)
TPM2_Sign (hash CSR_LAK) (Private (AK local)).                                  (* 4 *)

Definition ownerFinalTpm : tpm_state :=
sign (hash CSR_LAK) (Private (AK local)) ::                       (* 4 *)
hash CSR_LAK ::                                                   (* 3 *)
sign (TPM2B_Attest (Public (AK local))) (Private (AK initial)) :: (* 1 *)
ownerIniTpm.

Definition ownerFinal : state :=
sign (hash CSR_LAK) (Private (AK local)) ::                       (* 4 *)
hash CSR_LAK ::                                                   (* 3 *)
CSR_LAK ::                                                        (* 2 *)
sign (TPM2B_Attest (Public (AK local))) (Private (AK initial)) :: (* 1 *)
ownerIni. 

Hint Unfold ownerFinalTpm ownerFinal ownerIniTpm ownerIni ownerSteps  : core.

(* 0 - 4 *)
Theorem correct_ownerFinal :
execute (ownerIniTpm, ownerIni) ownerSteps (ownerFinalTpm, ownerFinal).
Proof.
  autounfold; repeat execute_constructor; simpl; auto.
Qed.

Hint Resolve correct_ownerFinal : core.

(*
send (CSR_LAK,, (sign (hash CSR_LAK) (Private (AK local))))   (* 5 *)
*)

Definition caOwnerIniTpm : tpm_state :=
[ key (Public (CA owner)) ;   (* Owner CA public *)
  key (Private (CA owner)) ]. (* Owner CA private *)

Definition caOwnerIni : state :=
[ key (Public (CA oem)) ;     (* OEM CA public *)
  key (Public (CA owner)) ;
  key (Private (CA owner)) ].

Definition caOwnerSteps : command :=
CheckHash (hash CSR_LAK) CSR_LAK ;;                                       (* 6a *)
CheckSig (sign (hash CSR_LAK) (Private (AK local)))                       (* 6b *)
         (Public (AK local)) ;;
CheckSig (sign (TPM2B_Attest (Public (AK local))) (Private (AK initial))) (* 6c *)
         (Public (AK initial)) ;;
CheckSig (sign (certificate (Public (AK initial))) (Private (CA oem)))    (* 6d *)
         (Public (CA oem)) ;;
MakeCert (Public (AK local)) (Private (CA owner)).                        (* 7 *)

Definition caOwnerFinalTpm : tpm_state :=
sign (certificate (Public (AK local))) (Private (CA owner)) ::  (* 7 *)
caOwnerIniTpm.

Definition caOwnerFinal : state :=
sign (certificate (Public (AK local))) (Private (CA owner)) ::  (* 7 *)
send (CSR_LAK,, (sign (hash CSR_LAK) (Private (AK local)))) ++  (* 5 *)
caOwnerIni.

Hint Unfold caOwnerFinalTpm caOwnerFinal caOwnerIniTpm caOwnerIni caOwnerSteps : core.

(* 0 - 7 *)
Theorem CertLAK_spec :
execute (ownerIniTpm, ownerIni) ownerSteps (ownerFinalTpm, ownerFinal) /\
In CSR_LAK ownerFinal /\
In (sign (hash CSR_LAK) (Private (AK local))) ownerFinal /\
execute (caOwnerIniTpm, send (CSR_LAK,, sign (hash CSR_LAK) (Private (AK local))) ++ caOwnerIni)
         caOwnerSteps 
        (caOwnerFinalTpm, caOwnerFinal).
Proof.
  repeat split; autounfold; repeat execute_constructor; simpl; auto 12.
Qed.







(* OEM creation of IAK certificate based on EK certificate *)
(* ******************************************************* *)

(* Numerical comment tags correspond to respective steps in latex documentation *)
Definition oemIniTpm : tpm_state :=
[ key (Public (AK initial)) ;   (* IAK public *)
  key (Private (AK initial)) ;  (* IAK private *)
  key (Private EK) ].           (* EK private *)

Definition oemIni : state :=
[ key (Public (AK initial)) ;
  key (Private (AK initial)) ;
  sign (certificate (Public EK)) (Private (CA tm)) ;  (* EK certificate *)
  key (Private EK) ].  

(* Certificate Signing Request for initial attestion key *)
Definition CSR_IAK : message :=
TCG_CSR_IDevID
  (sign (certificate (Public EK)) (Private (CA tm)))  (* EK certificate *)
  (key (Public (AK initial))).                        (* IAK public *)

Definition oemSteps1 : command :=
MakeCSR_IDevID (sign (certificate (Public EK)) (Private (CA tm))) (* 1 *)
               (Public (AK initial)) ;;
TPM2_Hash CSR_IAK ;;                                              (* 2 *)
TPM2_Sign (hash CSR_IAK) (Private (AK initial)).                  (* 3 *)

Definition oemMidTpm : state :=
sign (hash CSR_IAK) (Private (AK initial)) :: (* 3 *)
hash CSR_IAK ::                               (* 2 *)
oemIniTpm.

Definition oemMid : state :=
sign (hash CSR_IAK) (Private (AK initial)) :: (* 3 *)
hash CSR_IAK ::                               (* 2 *)
CSR_IAK ::                                    (* 1 *)
oemIni.

Hint Unfold oemMidTpm oemMid oemIniTpm oemIni oemSteps1 : core.

(* 0 - 3 *)
Theorem correct_oemMid :
execute (oemIniTpm, oemIni) oemSteps1 (oemMidTpm, oemMid).
Proof.
  autounfold; repeat execute_constructor; simpl; auto.
Qed.

Hint Resolve correct_oemMid : core.


(*
send (CSR_IAK,, (sign (hash CSR_IAK) (Private (AK initial))))   (* 4 *)
*)

Definition caOemIniTpm : tpm_state :=
[ key (Public (CA oem)) ;   (* OEM CA public *)
  key (Private (CA oem)) ]. (* OEM CA private *)


Definition caOemIni : state :=
[ key (Public (CA tm)) ;    (* TM CA public*)
  key (Public (CA oem)) ;
  key (Private (CA oem)) ].

Definition r : randType := 5.

Definition caOemSteps1 : command :=
CheckHash (hash CSR_IAK) CSR_IAK ;;                                   (* 5a *)
CheckSig (sign (hash CSR_IAK) (Private (AK initial)))                 (* 5b *)
         (Public (AK initial)) ;;
CheckSig (sign (certificate (Public EK)) (Private (CA tm)))           (* 5c *)
         (Public (CA tm)) ;;
TPM2_Hash (key (Public (AK initial))) ;;                              (* 6 *)
TPM2_GetRandom r ;;                                                   (* 7 *)
TPM2_MakeCredential (hash (key (Public (AK initial)))) r (Public EK). (* 8 *)

Definition caOemMidTpm : tpm_state :=
encrypt (credential (hash (key (Public (AK initial)))) r) (Public EK) ::  (* 8 *)
rand r ::                                                                 (* 7 *)
hash (key (Public (AK initial))) ::                                       (* 6 *)
caOemIniTpm.

Definition caOemMid : state :=
encrypt (credential (hash (key (Public (AK initial)))) r) (Public EK) ::  (* 8 *)
rand r ::                                                                 (* 7 *)
hash (key (Public (AK initial))) ::                                       (* 6 *)
send (CSR_IAK,, (sign (hash CSR_IAK) (Private (AK initial)))) ++          (* 4 *)
caOemIni.

Hint Unfold caOemMidTpm caOemMid caOemIniTpm caOemIni caOemSteps1 : core. 

(* 0 - 8 *)
Theorem correct_caOemMid :
execute (oemIniTpm, oemIni) oemSteps1 (oemMidTpm, oemMid) /\
In CSR_IAK oemMid /\
In (sign (hash CSR_IAK) (Private (AK initial))) oemMid /\
execute (caOemIniTpm, send (CSR_IAK,, sign (hash CSR_IAK) (Private (AK initial))) ++ caOemIni)
         caOemSteps1
        (caOemMidTpm, caOemMid).
Proof.
  repeat split; autounfold; repeat execute_constructor; simpl; auto 10.
Qed.

Hint Resolve correct_caOemMid : core.

(*
send (encrypt (credential (hash (key (Public (AK initial)))) r) (Public EK))   (* 9 *)
*)

Definition oemSteps2 (r' : randType) : command :=
TPM2_ActivateCredential (encrypt (credential (hash (key (Public (AK initial)))) r') (Public EK))  (* 10 *)
                        (Private EK)
                        (Private (AK initial)).

Definition oemFinalTpm (r' : randType) : tpm_state :=
(rand r') ::                                            (* 10 *)
(credential (hash (key (Public (AK initial)))) r') ::   (* 10 *)
oemMidTpm.

Definition oemFinal (r' : randType) : state :=
rand r' ::                                                                        (* 10 *)
credential (hash (key (Public (AK initial)))) r' ::                               (* 10 *)
send (encrypt (credential (hash (key (Public (AK initial)))) r') (Public EK)) ++  (* 9 *)
oemMid.

(*
send (rand r')    (* 11 *)
*)

Definition caOemSteps2 (r' : randType) : command :=
CheckNonce (rand r') r ;;                           (* 12 *)
MakeCert (Public (AK initial)) (Private (CA oem)).  (* 13 *)

Definition caOemFinalTpm : state := 
sign (certificate (Public (AK initial))) (Private (CA oem)) ::  (* 13 *)
caOemMidTpm.

Definition caOemFinal (r' : randType) : state := 
sign (certificate (Public (AK initial))) (Private (CA oem)) ::  (* 13 *)
send (rand r') ++                                               (* 11 *)
caOemMid.

Hint Unfold oemFinalTpm oemFinal oemSteps2 : core.
Hint Unfold caOemFinalTpm caOemFinal caOemSteps2 : core.

(* 0 - 13 *)
Theorem CertIAK_spec :
execute (oemIniTpm, oemIni) oemSteps1 (oemMidTpm, oemMid) /\
In CSR_IAK oemMid /\
In (sign (hash CSR_IAK) (Private (AK initial))) oemMid /\
execute (caOemIniTpm, send (CSR_IAK,, sign (hash CSR_IAK) (Private (AK initial))) ++ caOemIni)
         caOemSteps1
        (caOemMidTpm, caOemMid) /\
In (encrypt (credential (hash (key (Public (AK initial)))) r) (Public EK)) caOemMid /\
exists r',
execute (oemMidTpm, send (encrypt (credential (hash (key (Public (AK initial)))) r) (Public EK)) ++ oemMid) 
        (oemSteps2 r')
        (oemFinalTpm r', oemFinal r') /\
In (rand r') (oemFinal r') /\
execute (caOemMidTpm, send (rand r') ++ caOemMid)
        (caOemSteps2 r')
        (caOemFinalTpm, caOemFinal r').
Proof.
  repeat split; autounfold; try (exists r; repeat split); 
  repeat execute_constructor; simpl; auto 11.
Qed.

End KeyCert.