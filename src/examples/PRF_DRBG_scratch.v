
Set Implicit Arguments.

Require Import FCF.
Require Import HasDups.
Require Import RndInList.
Require Import CompFold.

Section DRBG.

(* Variable f : Key -> D -> Bvector eta. *)

(*   Fixpoint PRG_f (v : D) (n : nat) (key : Key) *)
(*              : list (Bvector eta) := *)
(*     match n with *)
(*       | O => nil *)
(*       (* he did it monadically *) *)
(*       | S n' => let res := f key v in *)
(*                 res :: PRG_f (injD res) n' key *)
(*     (* see, this is why you need the injection *) *)
(*     end. *)

(*   (* Comp bool *) *)
(* Variable Adv_DRBG : list (Bvector eta) -> Comp bool. *)

(* Indistinguishability definition for DRBGs *)
Section DRBG.

  (* The type of random seeds. *)
  Variable S : Set.
  Hypothesis S_EqDec : EqDec S.
  Variable RndS : Comp S.
  
  (* The type of DRBG outputs. *)
  Variable R : Set.
  Hypothesis R_EqDec : EqDec R.
  Variable RndR : Comp R.

  (* The DRBG *)
  (* well, one iteration of it, with no state? *)
  Variable f : S -> R.

  Variable A : R -> Comp bool.

  (* Pseudorandom *)
  Definition DRBG_G0 :=
    s <-$ RndS ;
    A (f s).

  (* Random *)
  Definition DRBG_G1 :=
    r <-$ RndR;
    A r.

  Definition DRBG_Advantage := | Pr[DRBG_G0] - Pr[DRBG_G1] |.

End DRBG.

Require Import PRF.

(* To keep things simple, we will assume that PRF outputs are bit vectors, and the DRBG output is a list of these bit vectors.  This setup can be generalized, if necessary.  *)
(* NOTE: a list of bit vectors, not a bvector or blist *)

(* We need an adaptively-secure PRF because we use the PRF output to produce the next input, and therefore this input is unpredictable. *)

Local Open Scope list_scope.
Local Opaque evalDist.

Section PRF_DRBG.

  Variable Key D : Set.
  (* The range of the PRF is a bit vector of length eta. *)
  Variable eta : nat.
  Hypothesis D_EqDec : EqDec D.

  Variable RndKey : Comp Key.

  (* f is an adaptively-secure PRF. (note: not PRG) *)
  Variable f : Key -> D -> Bvector eta.

  (* For this construction, we need an injection from the range of the PRF to the domain.  This allows us to use the previous PRF output to compute the next one. *)

  (* TODO: how do I say that "HMAC is" a PRF? *)
  (* In general, is the domain of the PRF not `Bvector eta`? *)
  Variable injD : Bvector eta -> D.
  Hypothesis injD_correct : 
    forall r1 r2, (injD r1) = (injD r2) -> r1 = r2.

  (* The length (in PRF output blocks) of the DRBG output is l.  This value must be positive. *)
  Variable l : nat.
  Hypothesis l_pos : l  > 0.

  (* Because the DRBG is constructed using feedback from the previous iteration, we need an initial value.  We assume an arbitrary bit vector and then inject it into the domain of the PRF.  This arrangement was chosen for simplicity, and it could easily be modified or generalized. *)
  Variable r_init : Bvector eta.
  Definition v_init := injD r_init.
  
  (* The computation used to obtain uniform random values in the range of the DRBG.  This computation is used only in the security definition. *)
(* Get a comp list of l blocks of {0,1}^eta (so they're each random?) *)
  Definition RndOut := compMap _ (fun _ => {0, 1}^eta) (forNats l).
  
  (* We model the DRBG using a function that uses the previous output value (injected into the domain) as the current input value of the PRF. *)
  (* f k would be a bit better as f_k *)

  Fixpoint PRF_DRBG_f (v : D)(n : nat)(k : Key) : list (Bvector eta) :=
    match n with
        | O => nil
        | S n' => 
          r <- (f k v);
            r :: (PRF_DRBG_f (injD r) n' k)
    end.

  (* This works, so no need to do it in Comp if it's not probabilistic *)
  Fixpoint PRG_f (v : D) (n : nat) (key : Key) : list (Bvector eta) :=
    match n with
    | O => nil
    | S n' => let r := f key v in
              r :: PRG_f (injD r) n' key
    end.

  Definition PRF_DRBG (k : Key) :=
    PRF_DRBG_f v_init l k.
  
  (* The adversary against the DRBG. *)
  Variable A : list (Bvector eta) -> Comp bool. (* no OracleComp *)
  Hypothesis A_wf : forall c, well_formed_comp (A c).

  Definition PRF_DRBG_G1 :=
    k <-$ RndKey;
    A (PRF_DRBG k).

  (* This is the generic DRBG defined as f : S -> R and A : R -> Comp bool. Guess we're saying it's equivalent to the fancier DRBG defined with the PRF and recursion *)
  (* Definition DRBG_G0 := *)
  (*   s <-$ RndS; *)
  (*   A (f s). *)
  Check DRBG_G0.

  (* Proving that the instantiated security def is equal to this exterior game *)
Theorem PRF_DRBG_G1_equiv :
  Pr[PRF_DRBG_G1] == Pr[DRBG_G0 RndKey PRF_DRBG A].
    Proof.
      reflexivity.
    Qed.

    (* Step 2: Use the PRF as an oracle. *)

    (* 5 definitions, 4 theorems *)

    (* result in comp? *)
    Check (ret nil).
    Check ($ ret nil).
    (* OracleComp A B (list C)
 *)
    (* IMPORTANT: the key is now hidden! (how?) *)
    Fixpoint PRF_DRBG_f_G2 (v : D) (n : nat) :
      (* OracleComp Key (D -> Bvector eta) *)
      OracleComp D (Bvector eta)
                 (list (Bvector eta))
      :=
      match n with
        | O => $ ret nil
        | S n' =>
          (* either one works -- why? *)
          (* r <- f key v;         (* TODO changed *) *)
          r <--$ OC_Query _ v;
          ls' <--$ PRF_DRBG_f_G2 (injD r) n';
          $ ret (r :: ls')
      end.

(* Variable v : nat. *)
(* Check (r <--$ OC_Query _ v; $ ret r). *)
Print OC_Query.
Check OC_Query.
Check f.
(* TODO: ask adam about the OC_Query above *)

(* note PRF adversary, not PRG adversary?
 this seems to still be the PRG adversary, just with the PRF as an oracle...*)
(* note bool not comp bool *)
    (* Definition PRF_A : OracleComp D (Bvector eta) bool := *)
    (*   k <-$ RndKey; *)
(*   A (f k v_init).           (* wrong A *) *)

Check A.                        (* list (Bvector eta) -> Comp bool *)
(* make sure you understand the difference between an adversary and a game *)
(* note difference between ($ (A ls)) and ($ ret (A ls)) -- see PRF_DRBG_f_G2 ending -- because the adversary itself returns a Comp bool? where does that go? *)
(* trapped in the OracleComp monad
note how the type changes from
OC D (Bvector eta) (list (Bvector eta)) 
to
OC D (Bvector eta) bool -- $ might invisibly take a comp and slot it into the OC type thing -- this is OC composition! (?) *)

(* Variable keyt : Key.            (* ??? *) *)
    Definition PRF_A : OracleComp D (Bvector eta) bool :=
      (ls <--$ PRF_DRBG_f_G2 v_init l ;
      $ A ls).
      
    (* skip *)
 Theorem PRF_DRBG_f_G2_wf : 
    forall n v,
      well_formed_oc (PRF_DRBG_f_G2 v n). 
        (* TODO well-formed proofs + this could be easily automated*)

    induction n; intuition; simpl in *.
    econstructor.
    wftac.
    econstructor.
    econstructor.
    intuition.
    econstructor.
    eauto.
    intuition.
    econstructor.
    wftac.
  Qed.

  Theorem PRF_A_wf : well_formed_oc PRF_A.

    unfold PRF_A.
    econstructor.
    apply PRF_DRBG_f_G2_wf.
    intuition.
    econstructor.
    apply A_wf.
  Qed.

  Locate f_oracle.              (* in PRF.f_oracle *)
  Check f_oracle.
  
Check PRF_A.                    (* TODO how to fill in these params?? *)
Check f_oracle.

  Definition PRF_DRBG_G2 :=
    s <-$ RndKey;
    [b, _] <-$2 PRF_A _ _ (f_oracle f _ s) tt;
    ret b.

  (* a function *)
  Fixpoint PRF_DRBG_f_G1_1 (v : D) (n : nat) (k : Key) : Comp (list (Bvector eta)):=
    match n with
      | O => ret nil
      | S n' =>
        r <-$ ret (f k v);
        ls <-$ PRF_DRBG_f_G1_1 (injD r) n' k;
        ret (r :: ls)
    end.

  (* another game using the new function *)
  Definition PRF_DRBG_G1_1 :=
    s <-$ RndKey;
    ls <-$ PRF_DRBG_f_G1_1 v_init l s;
    A ls.

  Print PRF_A.
  Print PRF_DRBG_f_G2.          (* using OC_Query *)
      (* note difference between G2 and G1_1:
G2 passes f_oracle to PRF_A which passes it to the oracle-query PRF_DRBG function, and gives the result to A

G1_1 is basically the same as G but just with another monad *)

  (* Definition PRF_DRBG_G1 := *)
  (*   k <-$ RndKey; *)
  (*   A (PRF_DRBG k). *)

  Theorem PRF_DRBG_G1_1_equiv :
    Pr[PRF_DRBG_G1] == Pr[PRF_DRBG_G1_1].
  Proof.
    unfold PRF_DRBG_G1.
    unfold PRF_DRBG_G1_1.
    comp_skip.

    fcf_to_prhl_eq.
    
    
    unfold PRF_DRBG. unfold PRF_DRBG_f.
    unfold PRF_DRBG_f_G1_1.
    
    
  Admitted.

  (* Goal *)
  Theorem PRF_DRBG_G1_G2_equiv :
    Pr[ PRF_DRBG_G1 ] == Pr[ PRF_DRBG_G2 ].
  Proof.
    rewrite PRF_DRBG_G1_1_equiv.
    unfold PRF_DRBG_G1_1.
    unfold PRF_DRBG_G2.
    
  Admitted.

    