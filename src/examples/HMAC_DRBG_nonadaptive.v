Set Implicit Arguments.

Require Import FCF.
(* RndInList has a useful theorem (qam_count) about counting calls to an oracle. *)
Require Import RndInList.
Require Import HasDups.
Require Import CompFold.
Require Import PRF.
Require Import OracleHybrid.
Require Import List.
Require Import PRF_DRBG.        (* note: had to move PRF_DRBG into FCF dir for this *)
Require Import Coq.Program.Wf.
Require Import OracleCompFold.

(* Shortcuts for FCF tactics *)
(* TODO remove / inline these *)
Ltac fs := fcf_simp.
Ltac fif := fcf_inline_first.
Ltac s := simpl.
Ltac fsr := fcf_spec_ret.
Ltac fskip := fcf_skip.

Theorem PRPL_demo : forall (n m : nat),
  comp_spec (fun a b => a = fst b)
            (x <-$ {0,1}^n;
             ret x)
            (c <-$ {0,1}^n;
             d <-$ {0,1}^m;
             ret (c,d)).
Proof.
  intros.
  fcf_skip. admit. admit. admit.

  fcf_irr_r.

  fcf_spec_ret.
Qed.

  (* TODO:

- Blist definitions X
- New for PRF-DRBG etc functions (instantiate, generate, update) X
- Make the correct oracles X
- Fill in the oracles with functions X

- Write the initial game and final game X
- Write the game i X
- Construct PRF adversary X
- Write the theorem statements (final theorem, inductive hypothesis) X

- Prove equivalence of the new GenUpdate oracle outputs (moving re-sampling v) to old GenUpdate oracle outputs X
- Apply the hybrid argument in G1_G2_close and make sure that theorem can be proven with Gi_Gi_plus_1_close X
- Move my proof to a separate file? or review it X
- Comment the uncommented games X

- Figure out what's going on with PRF advantage X
- Look at OracleMapHybrid (X)

- Write out all subgames (e.g. involving random functions) X
- Review step 4 and OracleHybrid proofs (X)
- Remove unneeded GenUpdate*_oc versions

- Prove G1 = Gi 0 and G2 = Gi q
- Prove Gi_prf (S i) = Gi_prg i
- Prove PRF advantage theorems
- Prove the theorems: (figure out what the main lemmas and difficulties are)
  - Pr[Collisions] = ? (for n+1 calls)
  - Apply Adam's argument

- Prove other things (well-formedness, etc. -- the hypotheses)
  - Deal with actual Instantiate (not just RB)
- Add backtracking resistance and prove that 
- Change to adaptive adversary?? (additional input, etc.)
*)

Local Open Scope list_scope.
Local Opaque evalDist.

(* --- Begin my HMAC-DRBG spec --- *)
Section PRG.

  (* note: the domain of the f is now Blist, not an abstract D
the key type is now also Bvector eta, since HMAC specifies that the key has the same size as the output (simplified) *)
Variable eta : nat.

(* Variable RndK : Comp (Bvector eta). *)
(* Variable RndV : Comp (Bvector eta). *)
(* TODO replace them *)
Definition RndK : Comp (Bvector eta) := {0,1}^eta.
Definition RndV : Comp (Bvector eta) := {0,1}^eta.

Variable f : Bvector eta -> Blist -> Bvector eta.

Definition KV : Set := (Bvector eta * Bvector eta)%type.
Hypothesis eqDecState : EqDec KV.
Variable eqdbv : EqDec (Bvector eta).
Variable eqdbl : EqDec Blist.

(* injection is to_list. TODO prove this *)
Variable injD : Bvector eta -> Blist.
Hypothesis injD_correct :
  forall r1 r2, injD r1 = injD r2 -> r1 = r2.

Definition to_list (A : Type) (n : nat) (v : Vector.t A n) := Vector.to_list v.

(* PRG functions *)

(* TODO does not reflect NIST spec *)
Definition Instantiate : Comp KV :=
  k <-$ RndK;
  v <-$ RndV;
  ret (k, v).

Print Comp.
SearchAbout Comp.
Locate "<-$". 

(* save the last v and output it as part of the state *)
Fixpoint Gen_loop (k : Bvector eta) (v : Bvector eta) (n : nat)
  : list (Bvector eta) * Bvector eta :=
  match n with
  | O => (nil, v)
  | S n' =>
    let v' := f k (to_list v) in
    let (bits, v'') := Gen_loop k v' n' in
    (v' :: bits, v'')           (* TODO change mine from (v ::) to (v ++), *or* prove indistinguishable (add another game in the beginning) *)
  end.

Theorem Gen_loop_test : forall k v, Gen_loop k v 3 =    (f k (to_list v)
    :: f k (to_list (f k (to_list v)))
       :: f k (to_list (f k (to_list (f k (to_list v))))) :: nil,
   f k (to_list (f k (to_list (f k (to_list v)))))).
Proof.
  reflexivity.
Qed.

(* Generate + Update *)
(* This has oracle type:
state: k, v
input: n
output: list (Bvector eta)
state: k, v *)

(* Spec says "V || 0x00"; here we will use a list of 8 bits of 0 (a byte) *)
Fixpoint replicate {A} (n : nat) (a : A) : list A :=
  match n with
  | O => nil
  | S n' => a :: replicate n' a
  end.

Definition zeroes : list bool := replicate 8 true.

(* oracle 1 *)

(* do not use; here as reference implementation so we can prove 
[GenUpdate_original, GenUpdate_original, ...] = [GenUpdate_noV, GenUpdate, Genupdate, ...] *)
Definition GenUpdate_original (state : KV) (n : nat) :
  Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  [bits, v'] <-2 Gen_loop k v n;
  k' <- f k (to_list v' ++ zeroes);
  v'' <- f k' (to_list v');
  ret (bits, (k', v'')).

(* want to change to this, and prove the outputs are the same. 
the other GenUpdates don't use this version *)
Definition GenUpdate (state : KV) (n : nat) :
  Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  v' <- f k (to_list v);
  [bits, v''] <-2 Gen_loop k v' n;
  k' <- f k (to_list v'' ++ zeroes);
  ret (bits, (k', v'')).

(* use this for the first call *)
Definition GenUpdate_noV (state : KV) (n : nat) :
  Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  [bits, v'] <-2 Gen_loop k v n;
  k' <- f k (to_list v' ++ zeroes);
  ret (bits, (k', v')).

(* --- End my HMAC-DRBG spec --- *)
(* well, this doesn't include the "sequence of executions" business, which happens in the games *)

(* oracle 2: all PRFs replaced with random bits *)
(* TODO: intermediate oracles, each with random functions *)

(* intermediates have unnecessary state and updating of the state to match earlier ones *)
Fixpoint Gen_loop_rb_intermediate (k : Bvector eta) (v : Bvector eta) (n : nat)
  : Comp (list (Bvector eta) * Bvector eta) :=
  match n with
  | O => ret (nil, v)
  | S n' =>
    v' <-$ {0,1}^eta;
    [bits, v''] <-$2 Gen_loop_rb_intermediate k v' n';
    ret (v' :: bits, v'')
  end.

(* final versions (without unnecessary (k, v) updating) *)
Fixpoint Gen_loop_rb (n : nat) : Comp (list (Bvector eta)) :=
  match n with
  | O => ret nil
  | S n' =>
    v' <-$ {0,1}^eta;
    bits <-$ Gen_loop_rb n';
    ret (v' :: bits)
  end.

(* passes the state around to match the types in Oi_oc' *)
Definition GenUpdate_rb_intermediate (state : KV) (n : nat) 
  : Comp (list (Bvector eta) * KV) :=
  bits <-$ Gen_loop_rb n;
  ret (bits, state).

Definition GenUpdate_rb_oracle (tt : unit) (n : nat) : Comp (list (Bvector eta) * unit) :=
  bits <-$ Gen_loop_rb n;
  ret (bits, tt).

Definition GenUpdate_rb (n : nat) : Comp (list (Bvector eta)) :=
  bits <-$ Gen_loop_rb n;
  ret bits.

(* TODO: prove well_formed for the oracles *)

(* Non-adaptive adversary. Consequently, does not use OracleComp, because it won't be adjusting its input to the GenUpdate oracle (number of blocks requested from Gen_loop) based on the GenUpdate oracle's output, because the number of blocks and queries is fixed. *)
Variable A : list (list (Bvector eta)) -> Comp bool.
Hypothesis A_wf : forall ls, well_formed_comp (A ls).

Variable blocksPerCall : nat.       (* blocks generated by GenLoop *)
Variable numCalls : nat.        (* number of calls to GenUpdate *)
Hypothesis H_numCalls : numCalls > 0. (* need this for GenUpdate equivalence? *)
Definition maxCallsAndBlocks : list nat := replicate numCalls blocksPerCall.

(* Change to an abstract, nonempty list. *)
(* TODO: change name *)
(* Parameter firstCall : nat. *)
(* Parameter blocksForCalls_2 : list nat. *)
(* Definition maxCallsAndBlocks : list nat := firstCall :: blocksForCalls_2. *)
(* used with oracleMap: call the oracle numCalls times, each time requesting blocksPerCall blocks *)

(* only first call uses GenUpdate_noV; assumes numCalls > 0 *)
Definition G1_prg : Comp bool :=
  [k, v] <-$2 Instantiate;
  [head_bits, state'] <-$2 GenUpdate_noV (k, v) blocksPerCall;
  [tail_bits, _] <-$2 oracleMap _ _ GenUpdate state' (tail maxCallsAndBlocks);
  A (head_bits :: tail_bits).

(* TODO: backtracking resistance? for nonadaptive adversary *)
(* Definition G1_prg_br : Comp bool :=
  blocksForEachCall <- A1; (* implicitly compromises after that # calls *)
  [k, v] <-$2 Instantiate;
  [head_bits, state'] <-$2 GenUpdate_noV (k, v) (head blocksForEachCall);
  [tail_bits, state''] <-$2 oracleMap _ _ GenUpdate state' (tail blocksForEachCall);
  [k', v'] <-$ UpdateV state'';
  A2 (head_bits :: tail_bits, (k', v')). *)

(* rand bits *)
(* Definition G2_prg_br : Comp bool :=
  blocksForEachCall <- A1;
  [bits, state'] <-$2 oracleMap _ _ GenUpdate_rb (k, v) blocksPerCall;
  k <- {0,1}^eta;
  v <- {0,1}^eta;
  A2 (head_bits :: tail_bits, (k, v)). *)

(* --------------------- *)
(* Prove v-update move equivalence *)

(* calling (GenUpdate_original, GenUpdate_original, ...) should have the same output
as calling (GenUpdate_noV, GenUpdate, GenUpdate, ...) which moves the v-update to the beginning of the next oracle call *)
(* proof outline: G1_prg_original = G1_prg_original_split ~ G1_prg *)

Definition G1_prg_original : Comp bool :=
  [k, v] <-$2 Instantiate;
  [bits, _] <-$2 oracleMap _ _ GenUpdate_original (k, v) maxCallsAndBlocks;
  A bits.

(* make the form closer to G1_prg by splitting off first call only *)
Definition G1_prg_original_split : Comp bool :=
  [k, v] <-$2 Instantiate;
  [head_bits, state'] <-$2 GenUpdate_original (k, v) blocksPerCall;
  [tail_bits, _] <-$2 oracleMap _ _ GenUpdate_original state' (tail maxCallsAndBlocks);
  A (head_bits :: tail_bits).

(* use version that's better for induction *)

(* oracleMap hardcodes acc for compFold as nil, so generalize it *)
Theorem compFold_acc : forall numCalls bits acc state,
   comp_spec
     (fun x y : list (list (Bvector eta)) * KV =>
      hd_error (fst x) = Some bits /\ tl (fst x) = fst y)
     (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) eqDecState)
        (fun (acc : list (list (Bvector eta)) * KV) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ GenUpdate_original s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (bits :: acc, state) (replicate numCalls blocksPerCall))
     (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) eqDecState)
        (fun (acc : list (list (Bvector eta)) * KV) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ GenUpdate_original s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (acc, state) (replicate numCalls blocksPerCall)).
Proof.
  destruct numCalls as [ | numCalls'].
  inversion H_numCalls.
  intros. revert bits acc state.
  induction numCalls0; intros.

  - simpl. fcf_spec_ret.
  - simpl.
    fcf_inline_first. fcf_skip.
    remember a0 as bits1. remember b as state'. clear Heqbits1 Heqstate'.
    fcf_simp.
    apply IHnumCalls0.
Qed.

(* do first call of map separately *)
Theorem GenUpdate_split_close :
  Pr[G1_prg_original] == Pr[G1_prg_original_split].
Proof.
  unfold G1_prg_original, G1_prg_original_split.
  unfold maxCallsAndBlocks.
  destruct numCalls as [ | numCalls'].
  * inversion H_numCalls.
  * Opaque GenUpdate_original. 
    simpl.
    fcf_to_prhl_eq.
    fcf_skip.
    fcf_simp.
    remember b as k. remember b0 as v. clear Heqk Heqv.
    remember (replicate numCalls' blocksPerCall) as maxCallsAndBlocks'.

    unfold oracleMap. simpl.
    fcf_inline_first.
    fcf_skip.
    Opaque getSupport. simpl in *.
    remember a0 as bits. remember b1 as state'. clear Heqbits Heqstate'.

    fcf_skip.
    instantiate (1 := (fun x y => hd_error (fst x) = Some bits /\ tail (fst x) = fst y)).
    - apply compFold_acc.
    - fcf_simp. simpl in H5. inversion H5. clear H5. destruct a1. inversion H6. simpl in *. inversion H6. subst. fcf_reflexivity.
      Transparent GenUpdate_original.
Qed.

(* generalize acc again. could be generalized further for the function on v but oh well *)
Theorem comp_spec_acc_2 : forall numCalls acc k v,
 comp_spec (fun x y : list (list (Bvector eta)) * KV => fst x = fst y)
     (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) eqDecState)
        (fun (acc : list (list (Bvector eta)) * KV) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ GenUpdate_original s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (acc,
        (k, f k (to_list v)))
        (replicate numCalls blocksPerCall))
     (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) eqDecState)
        (fun (acc : list (list (Bvector eta)) * KV) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ GenUpdate s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (acc, (k, v))
        (replicate numCalls blocksPerCall)).
Proof.
  intros.
  destruct numCalls. inversion H_numCalls.
  revert v k acc. induction numCalls0 as [ | numCalls']; intros.
  * simpl. fcf_spec_ret.
  * simpl.
    fcf_inline_first. fcf_simp. apply IHnumCalls'.
Qed.

(* G1_prg_original: calls GenUpdate_original, then GenUpdate_original
G1_prg: uses GenUpdate_noV, then GenUpdate (v moved) *)
Theorem GenUpdate_v_output_probability :
  Pr[G1_prg_original] == Pr[G1_prg].
Proof.
  rewrite GenUpdate_split_close.
  unfold G1_prg_original_split, G1_prg.
  fcf_to_prhl_eq.
  fcf_skip.
  fcf_simp.
  remember b as k. remember b0 as v. clear Heqk Heqv.
  simpl.
  fcf_inline_first.
  fcf_simp.
  remember (to_list b1 ++ zeroes) as v1_pad.
  unfold maxCallsAndBlocks.

  destruct numCalls as [ | numCalls'].

  * inversion H_numCalls.
  * simpl.
    fcf_skip.
    instantiate (1 := (fun x y => fst x = fst y)).
    unfold oracleMap.

    - apply comp_spec_acc_2.

    - fcf_simp. simpl in *. subst. fcf_reflexivity.
Qed.

(* End proofs of v-update equivalence *)
(* ------------------------------------------------ *)

(* TODO: intermediate games with random functions and random bits *)

(* uses simplified RB versions *)
Definition G2_prg' : Comp bool :=
  [bits, _] <-$2 oracleMap _ _ GenUpdate_rb_oracle tt maxCallsAndBlocks;
  A bits.

(* simpler version of GenUpdate only requires compMap. prove the two games equivalent *)
Definition G2_prg : Comp bool :=
  bits <-$ compMap _ GenUpdate_rb maxCallsAndBlocks;
  A bits.

(* oracle i *)
(* number of calls: first call is 0, last call is (numCalls - 1) for numCalls calls total
G0: PRF PRF PRF
G1: RB  PRF PRF
G2: RB  RB  PRF
G3: RB  RB  RB 
there should be (S numCalls) games, so games are numbered from 0 through numCalls *)
Definition Oi_prg (i : nat) (sn : nat * KV) (n : nat)
  : Comp (list (Bvector eta) * (nat * KV)) :=
  [callsSoFar, state] <-2 sn;
  let GenUpdate_choose := if lt_dec callsSoFar i (* callsSoFar < i (override all else) *)
                          then GenUpdate_rb_intermediate
                          (* first call does not update v, to make proving equiv. easier*)
                          else if beq_nat callsSoFar O then GenUpdate_noV
                          else GenUpdate in
  (* note: have to use intermediate, not final GenUpdate_rb here *)
  [bits, state'] <-$2 GenUpdate_choose state n;
  ret (bits, (S callsSoFar, state')).

(* game i (Gi 0 = G1 and Gi q = G2) *)
Definition Gi_prg (i : nat) : Comp bool :=
  [k, v] <-$2 Instantiate;
  [bits, _] <-$2 oracleMap _ _ (Oi_prg i) (O, (k, v)) maxCallsAndBlocks;
  A bits.


(* ------------------------------- *)
(* G1 is equal to first hybrid *)

(* move the non-nil init state inside compFold's init acc. otherwise, same compFold as in oracleMap *)
Definition G1_prg_fold : Comp bool :=
  [k, v] <-$2 Instantiate;
  [head_bits, state'] <-$2 GenUpdate_noV (k, v) blocksPerCall;
  (* unfolding the oracleMap *)
  (* [tail_bits, _] <-$2 oracleMap _ _ GenUpdate state' (tail maxCallsAndBlocks); *)
  [bits, _] <-$2 compFold _
            (fun acc d => [rs, s] <-2 acc;
             [r, s] <-$2 GenUpdate s d;
             ret (rs ++ r :: nil, s)) 
            (head_bits :: nil, state') (tail maxCallsAndBlocks);
  A bits.

Lemma compFold_acc_eq : forall (l : list nat) (a0 : list (Bvector eta)) (b1 : KV) (bits : list (list (Bvector eta))),
   comp_spec eq
     (z <-$
      compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) eqDecState)
        (fun (acc : list (list (Bvector eta)) * KV) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ GenUpdate s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (bits, b1) l;
      [tail_bits, _]<-2 z; A (a0 :: tail_bits))
     (z <-$
      compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) eqDecState)
        (fun (acc : list (list (Bvector eta)) * KV) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ GenUpdate s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (a0 :: bits, b1) l;
      [bits, _]<-2 z; A bits).
Proof.
  induction l as [ | call calls]; intros.

  * fcf_simp.
    fcf_reflexivity.
  * simpl.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    apply IHcalls.
Qed.

Lemma G1_G1_acc_equal :
  Pr[G1_prg] == Pr[G1_prg_fold].
Proof.
  fcf_to_prhl_eq.
  unfold G1_prg, G1_prg_fold.
  fcf_skip.
  fcf_simp.
  fcf_skip.
  unfold oracleMap.
  (* maybe induct on numCalls then use equality? *)
  unfold maxCallsAndBlocks.
  apply compFold_acc_eq.
Qed.

(* compFold with GenUpdate is the same as compFold with (Oi_prg 0) and # calls starting >=1 *)
Lemma compFold_GenUpdate_Oi_prg :
  forall (calls : list nat) (l : list (list (Bvector eta))) (k v : Bvector eta)
         (callsSoFar : nat),
    beq_nat callsSoFar 0%nat = false ->
   comp_spec
     (fun (x : list (list (Bvector eta)) * KV)
        (y : list (list (Bvector eta)) * (nat * KV)) =>
      x = (fst y, snd (snd y)))
     (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) eqDecState)
        (fun (acc : list (list (Bvector eta)) * KV) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ GenUpdate s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (l, (k, v)) calls)
     (compFold
        (pair_EqDec (list_EqDec (list_EqDec eqdbv))
           (pair_EqDec nat_EqDec eqDecState))
        (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ Oi_prg 0 s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (l, (callsSoFar, (k, v))) calls).
Proof.
  induction calls as [ | call calls']; intros.
  * simpl.
    fcf_spec_ret.
  * simpl.
    destruct (beq_nat callsSoFar 0).
    - inversion H.
    - simpl.
      fcf_inline_first.
      fcf_simp.
      apply IHcalls'.
      auto.
Qed.

(* wait what? it needs identical until bad??? *)
(* TODO make sure the numbering is right *)
Lemma G1_Gi_O_equal :
  Pr[G1_prg] == Pr[Gi_prg O].
Proof.
  rewrite G1_G1_acc_equal.
  fcf_to_prhl_eq.
  unfold G1_prg_fold.
  unfold Gi_prg.

  (* Oi_prg 0 is ~ GenUpdate_noV, GenUpdate, GenUpdate, ...? *)
  unfold maxCallsAndBlocks.
  destruct numCalls.

  * inversion H_numCalls.

  * simpl.
    comp_skip.
    unfold oracleMap.
    simpl. (* break up latter oracleMap *)
    fs.
    fif.
    fs.
    (* maybe I can get the l out of the compFold? forgot how it works *)
    fcf_skip.
    instantiate (1 := (fun x y => x = (fst y, snd (snd y)))).
    (* simple generalize + induction *)
    apply compFold_GenUpdate_Oi_prg.
    auto.

    simpl in H3.
    inversion H3.
    subst.
    destruct b3.
    simpl.
    fcf_reflexivity.
Qed.

(* ----- G2 is equal to last hybrid. Helper lemmas *)

Open Scope nat.

(* relate map with fold where GenUpdate_rb_oracle is easier to prove things about than Oi_prg numCalls *)
Lemma compMap_compFold_rb_eq :
  forall (calls : list nat) (acc : list (list (Bvector eta))) (u : unit),
    comp_spec (fun x y => x = fst y)
              (ls <-$ compMap (list_EqDec eqdbv) GenUpdate_rb calls; ret (acc ++ ls))
              (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) unit_EqDec)
                        (fun (acc0 : list (list (Bvector eta)) * unit) (d : nat) =>
                           [rs, s]<-2 acc0;
                         z <-$ GenUpdate_rb_oracle s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
                        (acc, u) calls).
 Proof.
   induction calls as [ | call calls']; intros.
   * fcf_simp.
     fcf_spec_ret.
   * simpl.
     fcf_inline_first.
     fcf_skip.
     { instantiate (1 := (fun x y => x = fst y)).
     unfold GenUpdate_rb, GenUpdate_rb_oracle.
     fcf_skip.
     fcf_spec_ret. }
     fcf_inline_first.
     fcf_simp.
     simpl in *. subst.

     (* since fcf_rewrite_expr app_cons_eq doesn't work... *)
     assert (comp_spec eq
                       (a <-$ compMap (list_EqDec eqdbv) GenUpdate_rb calls';
                        ls <-$ ret l :: a; ret acc ++ ls)
                       (a <-$ compMap (list_EqDec eqdbv) GenUpdate_rb calls';
                        ret ((acc ++ l :: nil) ++ a))). fcf_skip.
     fcf_spec_ret.
     apply app_cons_eq.

     eapply comp_spec_eq_trans_l.
     apply H1.
     apply IHcalls'.
Qed.

 (* specific version *)
Lemma compMap_compFold_rb_eq_specific :
  forall (calls : list nat) (u : unit),
    comp_spec (fun x y => x = fst y)
              (compMap (list_EqDec eqdbv) GenUpdate_rb calls)
              (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) unit_EqDec)
                        (fun (acc0 : list (list (Bvector eta)) * unit) (d : nat) =>
                           [rs, s]<-2 acc0;
                         z <-$ GenUpdate_rb_oracle s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
                        (nil, u) calls). 
Proof.
  intros.
  eapply comp_spec_eq_trans_l.
  instantiate (1 := ((ls <-$ compMap (list_EqDec eqdbv) GenUpdate_rb calls; ret nil ++ ls))).
  - fcf_ident_expand_l.
    fcf_skip.
    fcf_spec_ret.
  - pose proof (compMap_compFold_rb_eq calls nil u).
    auto.
Qed.

Lemma G2_oracle_eq :
  Pr[G2_prg] == Pr[G2_prg'].
Proof.
  unfold G2_prg, G2_prg'.
  unfold oracleMap.
  fcf_to_prhl_eq.
  fcf_skip.
  apply compMap_compFold_rb_eq_specific.
  fcf_simp.
  simpl in *.
  subst.
  fcf_reflexivity.
Qed.

 (* extend the proof above to hold on (Oi_prg numCalls) using the invariant *)
Lemma compMap_oracleMap_rb :
  forall (calls : list nat) (k v : Bvector eta) (n : nat) (acc : list (list (Bvector eta))) (u : unit),
    (* nice invariant *)
    n + length calls = numCalls ->
        comp_spec
     (fun (x : list (list (Bvector eta)) * unit)
        (y : list (list (Bvector eta)) * (nat * KV)) => 
      fst x = fst y)
     (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) unit_EqDec)
        (fun (acc : list (list (Bvector eta)) * unit) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ (bits <-$ Gen_loop_rb d; ret (bits, s));
         [r, s0]<-2 z; ret (rs ++ r :: nil, s0)) (acc, u) calls)
     (compFold
        (pair_EqDec (list_EqDec (list_EqDec eqdbv))
           (pair_EqDec nat_EqDec eqDecState))
        (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ Oi_prg numCalls s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (acc, (n, (k, v))) calls).
(* comp_spec *)
(*   (fun (x : list (list (Bvector eta))) *)
(*      (y : list (list (Bvector eta)) * (nat * KV)) => x = fst y) *)
(* (ls <-$ compMap (list_EqDec eqdbv) GenUpdate_rb calls; ret acc ++ ls) *)
(* (compFold *)
(*    (pair_EqDec (list_EqDec (list_EqDec eqdbv)) *)
(*       (pair_EqDec nat_EqDec eqDecState)) *)
(*    (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) => *)
(*     [rs, s]<-2 acc; *)
(*     z <-$ Oi_prg numCalls s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0)) *)
(*    (acc, (n, (k, v))) calls). *)
Proof.
  induction calls as [ | call calls']; intros.
  * simpl.
    fcf_spec_ret.
  * simpl.
    fcf_inline_first.
    destruct (lt_dec n numCalls).

    (* n < numCalls *)
    - unfold GenUpdate_rb_intermediate.
      fcf_inline_first.
      fcf_skip. admit.
      fcf_simp.
      simpl in *.
      apply IHcalls'.
      omega.

    (* n >= numCalls: impossible *)
    - simpl in *. omega.
Qed.

Close Scope nat.

(* pull it out? *)
Lemma length_replicate : forall {A : Type} (n : nat) (x : A),
    length (replicate n x) = n.
Proof.
  induction n; intros.
  * reflexivity.
  * simpl. rewrite IHn. reflexivity.
Qed.  

(* G2 is equal to last hybrid *)
(* should be even easier than G1 since no GenUpdate_noV happening? Wrong *)
Lemma G2_Gi_n_equal :
  Pr[G2_prg] == Pr[Gi_prg numCalls].
Proof.
  rewrite G2_oracle_eq.
  fcf_to_prhl_eq.
  unfold G2_prg'.
  unfold Gi_prg.
  unfold GenUpdate_rb_oracle.
  (* prove something about Oi_prg with numCalls *)
  fcf_irr_r. 
  { unfold Instantiate. fcf_well_formed.
  unfold RndK. fcf_well_formed.
  unfold RndV. fcf_well_formed. }
  fcf_simp.
  rename b into k.
  rename b0 into v.
  fcf_skip.
  instantiate (1 := (fun x y => fst x = fst y)).

  (* note: switching between windows is C-x o *)
  - unfold oracleMap.
    apply compMap_oracleMap_rb.
    unfold maxCallsAndBlocks.
    simpl.
    apply length_replicate.

  - simpl in *.
    subst.
    fcf_simp.
    simpl.
    fcf_reflexivity.
Qed.

(* ---------------------------------- *)

(* For PRF adversary:

Gen_loop_oc: takes an oracle in place of (f k)

GenUpdate_oc: takes an oracle in place of (f k)

Oi_prg_rf: if n > i then query GenUpdate_rb, OC version
           else if n = i then query Gen_loop_oc with the given oracle (RF)
           else query GenUpdate, OC version (using PRF)

PRF_Adversary: gives the Oi oracle the (f k) oracle it's given by Gi, and queries the resulting oracle `maxCalls` times, querying `numBlocks` each time. passes the result to the existing (non-adaptive) GenUpdate adversary

Gi_rf: gives the PRF_Adversary the random function oracle and returns what PRF_Adversary returns

PRF_Advantage: defined in terms of PRF_Adversary, indexed by i 
(but PRF_Advantage should be the same for all i) *)

(* Versions of Gen_loop and GenUpdate with that query the oracle in place of (f k) *)
(* this is slightly different from Adam's version:

  Fixpoint PRF_DRBG_f_G2 (v : D)(n : nat) :
    OracleComp D (Bvector eta) (list (Bvector eta)) :=
    match n with
        | O => $ ret nil
        | S n' => 
          r <--$ (OC_Query _ v);
            ls' <--$ (PRF_DRBG_f_G2 (injD r) n');
                $ ret (r :: ls')
    end. *)
Fixpoint Gen_loop_oc (v : Bvector eta) (n : nat)
  : OracleComp (list bool) (Bvector eta) (list (Bvector eta) * Bvector eta) :=
  match n with
  | O => $ ret (nil, v)
  | S n' =>
    v' <--$ (OC_Query _ (to_list v)); (* ORACLE USE *)
    [bits, v''] <--$2 Gen_loop_oc v' n';
    $ ret (v' :: bits, v'')
  end.

(* TODO trying to figure out dependencies for PRF_DRBG. can i instantiate key D etc.? *)
Check dupProb_const.
Check PRF_DRBG_G3_bad_4_small.
Print PRF_DRBG_G3_bad_4.

(* takes in key but doesn't use it, to match the type of other GenUpdates *)
Definition GenUpdate_oc (state : KV) (n : nat) :
  OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) :=
  [k, v_0] <-2 state;
  v <--$ (OC_Query _ (to_list v_0)); (* ORACLE USE *)
  [bits, v'] <--$2 Gen_loop_oc v n;
  (* TODO what's the state type here? and the global GenUpdate_oc return type? *)
  k' <--$ (OC_Query _ (to_list v' ++ zeroes)); (* ORACLE USE *)
  $ ret (bits, (k', v')).

(* should use the oracle and ignore the passed-in k *)
Definition GenUpdate_noV_oc (state : KV) (n : nat) :
  OracleComp (list bool) (Bvector eta)  (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  [bits, v'] <--$2 Gen_loop_oc v n;
  (* TODO what's the state type here? and the global GenUpdate_oc return type? *)
  k' <--$ (OC_Query _ (to_list v' ++ zeroes)); (* ORACLE USE *)
  $ ret (bits, (k', v')).

(* doesn't use the oracle, uses the PRF *)
Definition GenUpdate_PRF_oc (state : KV) (n : nat) :
  OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  v' <- f k (to_list v);
  [bits, v''] <-2 Gen_loop k v' n;
  k' <- f k (to_list v'' ++ zeroes);
  $ ret (bits, (k', v'')).

(* doesn't use the state or oracle *)
(* intermediates have unnecessary state and updating of the state to match earlier ones *)
Definition GenUpdate_rb_intermediate_oc (state : KV) (n : nat) 
  : OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) :=
  bits <--$ $ Gen_loop_rb n;    (* promote comp to oraclecomp, then remove from o.c. *)
  $ ret (bits, state).

(* same as Oi_prg but each GenUpdate in it has been converted to OracleComp *)
(* number of calls starts at 0 and ends at q. e.g.
G1:      RB  PRF PRF
Gi_rf 1: RB  RF  PRF (i = 1 here)
G2:      RB  RB  PRF *)
(* number of calls: first call is 0, last call is (numCalls - 1) for numCalls calls total
G0: PRF PRF PRF <-- Gi_prf 0
    RF  PRF PRF <-- Gi_rf 0
G1: RB  PRF PRF <-- Gi_prf 1
    RB  RF  PRF <-- Gi_rf 1
G2: RB  RB  PRF
    RB  RB  RF
G3: RB  RB  RB  <-- note that there is no oracle slot to replace here
    RB  RB  RB  <-- likewise
there should be (S numCalls) games, so games are numbered from 0 through numCalls *)
(* there is always an oracle slot to replace until i >= numCalls *)

(* not entirely sure these are all the right cases / in the right order *)
(* i: index for oracle; callsSoFar; n *)
Definition Oi_oc' (i : nat) (sn : nat * KV) (n : nat) 
  : OracleComp Blist (Bvector eta) (list (Bvector eta) * (nat * KV)) :=
  [callsSoFar, state] <-2 sn;
  let GenUpdate_choose :=
      (* this behavior (applied with f_oracle) needs to match that of Oi_prg's *)
      if lt_dec callsSoFar i (* callsSoFar < i (override all else) *)
           then GenUpdate_rb_intermediate_oc (* this implicitly has no v to update *)
      else if beq_nat callsSoFar O (* use oracle on 1st call w/o updating v *)
           then GenUpdate_noV_oc 
      else if beq_nat callsSoFar i (* callsSoFar = i *)
           then GenUpdate_oc    (* uses provided oracle (PRF or RF) *)
      else GenUpdate_PRF_oc in        (* uses PRF with (k,v) updating *)
  [bits, state'] <--$2 GenUpdate_choose state n;
  $ ret (bits, (S callsSoFar, state')).

(* oracleCompMap_inner repeatedly applies the given oracle on the list of inputs (given an initial oracle state), collecting the outputs and final state *)
(* Fixpoint oracleCompMap_inner_acc {D R OracleIn OracleOut : Set}  *)
(*            (e1 : EqDec ((list R) * (nat * KV)))  *)
(*            (e2 : EqDec (list R)) *)
(*            (* this is an oracleComp, not an oracle *) *)
(*            (* the oracle has type (D * R) -> D -> Comp (R, (D * R)) *) *)
(*            (oracleComp : (nat * KV) -> D -> OracleComp OracleIn OracleOut (R * (nat * KV)))  *)
(*            (state : (nat * KV)) *)
(*            (init : list R) *)
(*            (inputs : list D) : OracleComp OracleIn OracleOut (list R * (nat * KV)) := *)
(*   match inputs with *)
(*   | nil => $ ret (init, state) *)
(*   | input :: inputs' =>  *)
(*     [res, state'] <--$2 oracleComp state input; (* doesn't use the init *) *)
(*     [resList, state''] <--$2 oracleCompMap_inner_acc _ _ oracleComp state' init inputs'; *)
(*     $ ret (init ++ res :: resList, state'') *)
(*   end. *)

(* Print compFold. *)
(* Print oracleMap. *)
(* Print oc_compMap. *)
(* compare to oc_compMap *)
(* maybe i don't even need to rewrite oracleCompMap_inner. what theorem do i really want? TODO *)

Fixpoint oracleCompMap_inner {D R OracleIn OracleOut : Set} 
           (e1 : EqDec ((list R) * (nat * KV))) 
           (e2 : EqDec (list R))
           (* this is an oracleComp, not an oracle *)
           (* the oracle has type (D * R) -> D -> Comp (R, (D * R)) *)
           (oracleComp : (nat * KV) -> D -> OracleComp OracleIn OracleOut (R * (nat * KV))) 
           (state : (nat * KV)) (* note this state type -- it is EXPLICITLY being passed around *)
           (inputs : list D) : OracleComp OracleIn OracleOut (list R * (nat * KV)) :=
  match inputs with
  | nil => $ ret (nil, state)
  | input :: inputs' => 
    [res, state'] <--$2 oracleComp state input;
    [resList, state''] <--$2 oracleCompMap_inner _ _ oracleComp state' inputs';
    $ ret (res :: resList, state'')
  end.

(* hides the oracle state from the caller. instantates the initial state and does not return the end state. need this, otherwise the PRF adversary has to generate the key and initial value (and can see it, which it shouldn't be able to) *)
Definition oracleCompMap_outer {D R OracleIn OracleOut : Set} 
           (e1 : EqDec ((list R) * (nat * KV))) 
           (e2 : EqDec (list R))
           (oracleComp : (nat * KV) -> D -> OracleComp OracleIn OracleOut (R * (nat * KV)))
           (inputs : list D) : OracleComp OracleIn OracleOut (list R) :=
  [k, v] <--$2 $ Instantiate;   (* generate state inside, instead of being passed state *)
  [bits, _] <--$2 oracleCompMap_inner _ _ oracleComp (O, (k, v)) inputs;
  (* the "_" here has type (nat * KV) *)
  $ ret bits.                    (* don't return the state to the PRF adversary *)

(* see long comment above this section *)
Definition PRF_Adversary (i : nat) : OracleComp Blist (Bvector eta) bool :=
  bits <--$ oracleCompMap_outer _ _ (Oi_oc' i) maxCallsAndBlocks;
  $ A bits.

(* ith game: use RF oracle *)
Definition Gi_rf (i : nat) : Comp bool :=
  [b, _] <-$2 PRF_Adversary i _ _ (randomFunc ({0,1}^eta) eqdbl) nil;
  ret b.

(* ith game: use PRF oracle *)
Definition Gi_prf (i : nat) : Comp bool :=
  k <-$ RndK;
  [b, _] <-$2 PRF_Adversary i _ _ (f_oracle f _ k) tt;
  ret b.

(* couldn't auto-prove this terminating, TODO fix this *)

(* Program Fixpoint segment' {A : Type} (n : nat) (l : list A) {measure (length (skipn n l))} *)
(*   : list (list A) := *)
(*   match n with *)
(*   | O => nil *)
(*   | S _ => firstn n l :: segment' n (skipn n l) *)
(*   end. *)
(* Solve All Obligations. *)
(* Next Obligation. *)
(* destruct l. *)
(* simpl. *)

(* [1,1,1,1,1] -> [[1,1,1] [1,1,1]] *)
(* TODO debug lennart's proof that proves termination *)
Open Scope nat.
Lemma skipn_length' {X : Type}: forall n (l:list X), length (skipn n l) <= length l.
Proof.
  induction n; simpl; intros. omega.
  destruct l. omega. specialize (IHn l); simpl. omega.
Qed.

Program Fixpoint segment {X : Type} (n : nat) (l : list X) {measure (length (skipn n l))}
  : list (list X) :=
  match l with
  | nil => nil
  | _ :: _ =>
    match n with
    | O => nil
    | S _ => firstn n l :: segment n (skipn n l)
    end
  end.
Solve All Obligations.          (* maybe the obligations are different? *)
Next Obligation.
  clear segment; simpl.
  rename wildcard' into a. rename wildcard'0 into l. rename wildcard'1 into n.
  specialize (skipn_length' n l). intros.
  (* omega. *)
Admitted.
Close Scope nat.

(* Expose the bad events *)

Definition hasInputDups (state : list (Blist * Bvector eta)) : bool :=
  hasDups _ (fst (split state)).

(* ith game: use RF oracle *)
Definition Gi_rf_bad (i : nat) : Comp (bool * bool) :=
  [b, state] <-$2 PRF_Adversary i _ _ (randomFunc ({0,1}^eta) eqdbl) nil;
  ret (b, hasInputDups state). 

Definition rb_oracle (state : list (Blist * Bvector eta)) (input : Blist) :=
  output <-$ ({0,1}^eta);
  ret (output, (input, output) :: state).

Definition Gi_rb (i : nat) : Comp bool :=
  [b, state] <-$2 PRF_Adversary i _ _ rb_oracle nil;
  let rbInputs := fst (split state) in
  ret b.

(* adam wrote a new game here -- bad event is repetition in the random INPUTS
INPUTS = v :: (first n of outputs)? *)
(* pass in the RB oracle that records its inputs
what about preceding/following RB and (especially) PRF inputs/outputs? *)
Definition Gi_rb_bad (i : nat) : Comp (bool * bool) :=
  [b, state] <-$2 PRF_Adversary i _ _ rb_oracle nil;
  ret (b, hasInputDups state). (* assumes ith element will exist, otherwise hasDups nil (default) = false *)

(* replace maxCallsAndBlocks with a list we can evaluate on *)
Definition PRF_Adversary_l (i : nat) (l : list nat) : OracleComp Blist (Bvector eta) bool :=
  bits <--$ oracleCompMap_outer _ _ (Oi_oc' i) l;
  $ A bits.

(* also replaced with hasDups: my hypothesis is that adam was right *)
Definition Gi_rf_bad_l (i : nat) (l : list nat) : Comp (bool * bool) :=
  [b, state] <-$2 PRF_Adversary_l i l _ _ (randomFunc ({0,1}^eta) eqdbl) nil;
  ret (b, hasInputDups state). (* assumes ith element will exist, otherwise hasDups nil (default) = false *)

Definition Gi_rb_bad_l (i : nat) (l : list nat) : Comp (bool * bool) :=
  [b, state] <-$2 PRF_Adversary_l i l _ _ rb_oracle nil;
  ret (b, hasDups _ state). (* assumes ith element will exist, otherwise hasDups nil (default) = false *)

(* Modeled after these definitions from PRF_DRBG.v *)
(*   Fixpoint PRF_DRBG_f_G2 (v : D)(n : nat) :
    OracleComp D (Bvector eta) (list (Bvector eta)) :=
    match n with
        | O => $ ret nil
        | S n' => 
          r <--$ (OC_Query _ v);
            ls' <--$ (PRF_DRBG_f_G2 (injD r) n');
                $ ret (r :: ls')    end.

  (* The constructed adversary against the PRF.
(takes something of type D -> Bvector eta, tries to guess whether it's RF or PRF)
the adversary can know the initial v, but not the K
   *)
  Definition PRF_A : OracleComp D (Bvector eta) bool :=
    ls <--$ PRF_DRBG_f_G2 v_init l;
    $ A ls. 

  Definition PRF_DRBG_G2 :=
    s <-$ RndKey ;
    [b, _] <-$2 PRF_A unit _ (f_oracle f _ s) tt;
    ret b.

  Definition PRF_DRBG_G3 :=
    [b, _] <-$2 PRF_A _ _ (randomFunc ({0,1}^eta) _) nil;
    ret b. *)


(* TODO: ok to be parametrized by i? *)
Definition PRF_Advantage_Game i : Rat := 
  PRF_Advantage RndK ({0,1}^eta) f eqdbl eqdbv (PRF_Adversary i).

Print PRF_Adversary.
Print PRF_Advantage.
Print PRF_G_A.
Print PRF_G_B.

(* should be the same for all i, arbitrarily choose 0 *)
Definition PRF_Advantage_i := PRF_Advantage_Game 0.

(*   | Pr  [PRF_G_A RndK f eqdbv (PRF_Adversary 0) ] -
   Pr  [PRF_G_B ({ 0 , 1 }^eta) eqdbl eqdbv (PRF_Adversary 0) ] | =
   | Pr  [PRF_G_A RndK f eqdbv (PRF_Adversary i) ] -
   Pr  [PRF_G_B ({ 0 , 1 }^eta) eqdbl eqdbv (PRF_Adversary i) ] | *)

(* TODO: are these lemmas even true? 
PA uses the existing adversary against the output?
here, numCalls = 4

PA 0: using given oracle for call 0
GA: PRF PRF PRF PRF?
GB:  RF PRF PRF PRF 

PA 1: using given oracle for call 1
GA: RB  PRF PRF PRF? 
GB: RB  RF  PRF PRF? 
(do the PRF_advantages add?)

PA n-2: using given oracle for call (n-2) = 2
GA: RB  RB  PRF PRF
GB: RB  RB  RF  PRF

PA n-1: using given oracle for call (n-1) = 3
GA: RB  RB  RB  PRF
GB: RB  RB  RB  RF

PA n: using given oracle for call n = 4
(note: there is no oracle to replace, so PRF_Advantage = 0)
GA: RB  RB  RB  RB
GB: RB  RB  RB  RB

forall i, i != n -> 
PRF_Advantage_Game i = PRF_Advantage_Game j
PRF_Advantage_Game n = 0

thus, forall i, PRF_Advantage_Game i <= PRF_Advantage_Game 0 *)

Open Scope nat.
(* could generalize this further to hold for any oracles, instead of f_oracle and RndR_func *)
Lemma Oi_numcalls_oracle_irrelevance : forall calls k v a (numCalls init : nat) acc tt,
    init + length calls = numCalls ->
   comp_spec
     (fun (x : list (list (Bvector eta)) * (nat * KV) * unit)
        (y : list (list (Bvector eta)) * (nat * KV) *
             list (Blist * Bvector eta)) => fst x = fst y)
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' numCalls) 
         (init, (k, v)) calls) unit unit_EqDec
        (f_oracle f eqdbv a) tt)
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' numCalls) 
         (init, (k, v)) calls) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv))
        (RndR_func ({ 0 , 1 }^eta) eqdbl) acc).
Proof.
(* didn't i do a gnarly proof just like this one earlier?? oh but it wasn't about oraclecompmap_inner. see 'G2 = last hybrid' proof*)
  induction calls as [ | call calls']; intros.
  - simpl.
    fcf_simp.
    fcf_spec_ret.
  - simpl in H.
    simpl.
    fcf_inline_first.
    fcf_skip. admit. admit.
    { instantiate (1 := (fun x y => fst x = fst y)).
      destruct (lt_dec init (init + S (length calls'))).
      * unfold GenUpdate_rb_intermediate_oc.
        simpl.
        fcf_inline_first.
        fcf_skip.
        admit. admit.
        fcf_simp.
        fcf_spec_ret.
      * omega.
    }
    simpl in H2.
    destruct b1.
    simpl in *.
    subst.
    fcf_inline_first.
    simpl.
    fcf_inline_first.
    fcf_simp.
    simpl.
    fcf_skip.
    destruct b0.                (* prevents unification *)
    apply IHcalls'.             (* lol *)
    omega.

    simpl in H3.
    destruct b2.
    simpl in *.
    subst.
    fcf_simp.
    fcf_spec_ret.
Qed.
Close Scope nat.

Lemma PRF_Advantage_0 : 
    PRF_Advantage_Game numCalls == 0.
Proof.
  intros. unfold PRF_Advantage_Game. unfold PRF_Advantage.
  assert (distance_0_eq : forall r1 r2 : Rat, r1 == r2 -> | r1 - r2 | == 0).
  { apply ratIdentityIndiscernables. }
  apply distance_0_eq. clear distance_0_eq.
  
  fcf_to_prhl_eq. (* TODO when should I *not* use this? *)

  (* TODO lemma that PRF_Advantage_Game numCalls always uses random bits and ignores the inputted oracle, so games A and B are on indistinguishable output *)

  unfold PRF_Adversary.
  unfold PRF_G_A.
  unfold PRF_G_B.

  fcf_irr_l. unfold RndK. fcf_well_formed.

  simpl.
  fcf_inline_first.
  fcf_skip.
  fcf_simp.
  simpl.
  fcf_inline_first.
  fcf_skip.

  (* arriving at oracleCompMap_inner: same but the oracles are different *)
  instantiate (1 := (fun x y => fst x = fst y)). (* TODO: forgot why this and not eq *)
  (* TODO: here, theorem about oracleCompMap_inner on maxCallsAndBlocks not using oracle (forall oracles A B...) *)

  *
    (* do i need induction? are there theorems about oracleCompMap (Adam's version)? *)
    unfold Oi_oc'.
    unfold oracleCompMap_inner.
    apply Oi_numcalls_oracle_irrelevance.
    simpl.
    unfold maxCallsAndBlocks.
    apply length_replicate.

  * simpl.
    fcf_simp.
    fcf_inline_first.
    simpl.
    fcf_inline_first.
    fcf_simp.
    fcf_inline_first.
    simpl in H4.
    inversion H4.
    subst.
    fcf_skip.
    fcf_simp. (* TODO ltac for this kind of proof *)
    fcf_reflexivity.
Qed.

(* is there an equivalent lemma i can prove that doesn't involve a probability difference?
i just need an upper bound...
can i just say, there exists some i for which PRF_Advantage_Game i is >= all others?? by properties of rational numbers? otherwise, contradiction. i think i can't actually do this in coq. *)
(* also is this lemma actually true?? *)
Lemma PRF_Advantages_same : forall (i j : nat),
    i <> numCalls -> j <> numCalls ->
    PRF_Advantage_Game i == PRF_Advantage_Game j.
Proof.
  intros i j i_neq j_neq.
  unfold PRF_Advantage_Game. unfold PRF_Advantage.
  (* do i even need this lemma? maybe there's an easier way *)
  (* i don't want to prove anything about differences in probability... *)
  (* should i use identical until bad?? i'm not sure if such a bad event exists, since PRF is totally opaque *)
(* split the absolute values the other way *)
  (* proof by contradiction? *)
  (* or i could prove a bunch of game equivalences on the first two and the last two, massaging them to look like each other (removing the extraneous RB and PRF), so then it would look like |a-b| == |a-b| *)
  (* what I really want to prove is: 
forall i, i <> numCalls -> 
PRF_Advantage_Game i = PRF_Advantage (the normal one with just the PRF/RF difference) 

(might have a special case for i=0) *)
  (* also i should look at the gnarly lemma before this and make sure it's true *)
  apply ratDistance_eqRat_compat.
  - unfold PRF_G_A.
    fcf_to_prhl_eq.
    fcf_skip.
    (* prove a different spec about PRF_Adversary i or j? *)
    unfold PRF_Adversary.
    simpl.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    simpl.
    fcf_inline_first.
    fcf_skip_eq.
    (* this is actually not true. this whole strategy is actually not true. *)
    admit.
  - unfold PRF_G_B.
    (* probably the same proof *)
    fcf_to_prhl_eq.
    admit.
Qed.

(* Lemma PRF_Advantages_lte : forall (i : nat), exists (j : nat), *)
(*     PRF_Advantage_Game i <= PRF_Advantage_Game j. *)
(* Proof. *)
(*   intros. *)
(*   intuition. *)

Lemma PRF_Advantages_lte : forall (i : nat),
    PRF_Advantage_Game i <= PRF_Advantage_Game 0.
Proof.
  intros.
  (* unfold PRF_Advantage_Game. *)
  (* TODO finish this using above two lemmas *)
  (* forgot how to do this more elegantly... *)
  assert (decide : i = numCalls \/ i <> numCalls). { omega. }
  destruct decide as [ i_eq | i_neq ].
  - subst.
    rewrite PRF_Advantage_0.
    unfold PRF_Advantage_Game.
    unfold PRF_Advantage.
    
    assert (absval_lowerbound : forall a b, 0 <= |a - b|).
    { intros.
      SearchAbout ratDistance.
      unfold ratDistance.
      SearchAbout ratSubtract.
      (* Locate "| _ - _ |". *)
      (* ok, this should be true for absolute value... *)
      admit.
    }
    apply absval_lowerbound.
  -
    assert (numCalls_neq_0 : 0%nat <> numCalls). omega.
    pose proof (PRF_Advantages_same i_neq numCalls_neq_0).
    rewrite H.
    SearchAbout bleRat.
    Print bleRat.
    unfold "<=".
    (* unfold bleRat. *)
    (* unfold ratCD. *)
    (* x <= x should be true... *)
    admit.
Qed.

(* base case theorem (adam's) TODO *)

(* Step 1 *)
(* Gi_prf 2: RB RB PRF PRF PRF
   Gi_rf 2:  RB RB RF  PRF PRF 
need to use `Gi_prf i` instead of `Gi_prg i` because this matches the form of 
`Gi_rf` closer so we can match the form of PRF_Advantage*)
Lemma Gi_prf_rf_close_i : forall (i : nat),
  | Pr[Gi_prf i] - Pr[Gi_rf i] | <= PRF_Advantage_Game i.
Proof.
  intros i.
  (* don't need to unfold *)
  unfold Gi_prf.
  unfold Gi_rf.
  unfold PRF_Advantage_Game.
  reflexivity. 
Qed.

Lemma Gi_prf_rf_close : forall (i : nat),
  | Pr[Gi_prf i] - Pr[Gi_rf i] | <= PRF_Advantage_i.
Proof.
  intros.
  eapply leRat_trans.
  apply Gi_prf_rf_close_i.
  unfold PRF_Advantage_i.
  apply PRF_Advantages_lte.
Qed.

(* ------------------------------- *)

(* Step 2 *)

(* TODO use Adam's existing theorem. not sure if this is the right bound.
should be a function of [blocksPerCall + 1] (for the extra v-update) *)
Definition Pr_collisions := (S blocksPerCall)^2 / 2^eta.

(* may need to update this w/ new proof *)
Definition Gi_Gi_plus_1_bound := PRF_Advantage_i + Pr_collisions.

(* These are all lemmas to rewrite games so I can apply identical until bad *)

Definition fst3 {A B C : Type} (abc : A * B * C) : A :=
  let (ab, c) := abc in
  let (a, b) := ab in
  a.

(* definition of equivalence relating oracleMap/oracleCompMap computations *)
Definition outputAndKVeq {A : Type} (x1 : A * (nat * KV))
        (x2 : A * (nat * KV) * unit) :=
  let (bits1, state1) := x1 in
  let (_, kv1) := state1 in

  let (res2, _) := x2 in
  let (bits2, state2) := res2 in
  let (_, kv2) := state2 in

  bits1 = bits2 /\ kv1 = kv2.   (* k and v? or k only? *)

Open Scope nat.

Ltac simplify :=
  repeat (try simpl; try fcf_inline_first; try fcf_simp).

(* These examples take a long time to check because of `simplify`. Commented out for now. *)

(* TODO move all Gi_normal_prf_eq work into a separate file *)
(*
(* n = 1, i = 0 *)
(* expect: PRF / PRF, but doesn't work?*)
(* n = 1, i = 1 -- expect RB / RB and *does* work *)
(* n = 2, i = 1 -- expect RB / PRF, but have no clue what's going on here *)
(* the "zooming in" lemma would actually really help here; should I use it instead? *)
Theorem Gi_normal_prf_eq_compspec_n1i0 : forall (k1 k2 v : Bvector eta),
    (* i <= length l -> *)
   comp_spec
     (fun (x : list (list (Bvector eta)) * (nat * KV))
        (y : list (list (Bvector eta)) * (nat * KV) * unit) =>
      fst x = fst3 y)
     (oracleMap (pair_EqDec nat_EqDec eqDecState) (list_EqDec eqdbv)
        (Oi_prg O) (O, (k1, v)) (2::nil) )
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv))
         (Oi_oc' O) 
         (O, (k2, v)) (2::nil) ) unit unit_EqDec
        (f_oracle f eqdbv k1) tt).
(* expect 1 run with 1 block generated by PRF only *)
Proof.
  intros.
  unfold oracleMap.
  simplify.
  (* TODO vulnerability: adversary needs to make at least 2 calls? *)
  (* (output list, (numCalls, (new K, **old** V, tt))) *)
  fcf_spec_ret.
Qed.                            (* fixed two bugs -- v-update order and oracle use *)

(* next: n2i1, n2i2 *)
(* it works for list [0,0], [1;0], and [1;1] *)
Theorem Gi_normal_prf_eq_compspec_n2i0 : forall (k1 k2 v : Bvector eta),
    (* i <= length l -> *)
   comp_spec
     (fun (x : list (list (Bvector eta)) * (nat * KV))
        (y : list (list (Bvector eta)) * (nat * KV) * unit) =>
      fst x = fst3 y)
     (oracleMap (pair_EqDec nat_EqDec eqDecState) (list_EqDec eqdbv)
        (Oi_prg O) (O, (k1, v)) (2::2::nil) )
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv))
         (Oi_oc' O) 
         (O, (k2, v)) (2::2::nil) ) unit unit_EqDec
        (f_oracle f eqdbv k1) tt).
(* expect 2 blocks, generated by PRF only *)
Proof.
  intros.
  unfold oracleMap.
  simplify.
  (* on the ith call, we use f_oracle with the original k1, and update the key to be (f k1 ...) for subsequent calls. note that the k2 we pass in originally is not used, and "overwritten" with (f k1 ...)
     for oracleMap, we start with k1 and update the key to be (f k1 ...) and so on
     so, the two computations are equal *)

  (* why are there so many f's in the second block of output? *)
  Print oracleMap.
  (* the fold goes backward, so uses ++; i use :: in oracleCompMap_inner *)
  fcf_spec_ret.
Qed.

(* Regression tests! *)

(* works for list [0,0], [1;0], and [1;1]? *)
(* expect RB / PRF *)
(* [0;0]: yes
[0;1]: yes, after fixing rb
[1;0]: yes, but with the comp_skip/admit stuff
[1;1]: yes, same as above *)
Theorem Gi_normal_prf_eq_compspec_n2i1 : forall (k1 k2 v : Bvector eta),
    (* i <= length l -> *)
   comp_spec
     (fun (x : list (list (Bvector eta)) * (nat * KV))
        (y : list (list (Bvector eta)) * (nat * KV) * unit) =>
      fst x = fst3 y)
     (oracleMap (pair_EqDec nat_EqDec eqDecState) (list_EqDec eqdbv)
        (Oi_prg 1) (O, (k1, v)) (2::1::nil) )
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv))
         (Oi_oc' 1) 
         (O, (k2, v)) (2::1::nil) ) unit unit_EqDec
        (f_oracle f eqdbv k1) tt).
Proof.
  intros.
  unfold oracleMap.
  simplify.
  unfold GenUpdate_rb_intermediate.
  unfold Gen_loop_rb.
  simplify.
  fcf_skip. admit. admit.
  simplify.
  fcf_skip. admit. admit.
  simplify.
  fcf_spec_ret.
Qed.

(* expect RB / RB *)
(* [1;1]: yes, but with two comp_skip/admits and unfolds *)
Theorem Gi_normal_prf_eq_compspec_n2i2 : forall (k1 k2 v : Bvector eta),
    (* i <= length l -> *)
   comp_spec
     (fun (x : list (list (Bvector eta)) * (nat * KV))
        (y : list (list (Bvector eta)) * (nat * KV) * unit) =>
      fst x = fst3 y)
     (oracleMap (pair_EqDec nat_EqDec eqDecState) (list_EqDec eqdbv)
        (Oi_prg 2) (O, (k1, v)) (2::1::nil) )
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv))
         (Oi_oc' 2) 
         (O, (k2, v)) (2::1::nil) ) unit unit_EqDec
        (f_oracle f eqdbv k1) tt).
Proof.
  intros.
  unfold oracleMap.
  simplify.
  unfold GenUpdate_rb_intermediate.
  unfold Gen_loop_rb.
  simplify.
  comp_skip. admit. admit.      (* what is this? *)
  simplify.
  unfold GenUpdate_rb_intermediate.
  unfold Gen_loop_rb.
  simplify.
  comp_skip. admit. admit.
  simplify.
  unfold GenUpdate_rb_intermediate.
  unfold Gen_loop_rb.
  simplify.
  comp_skip. admit. admit.
  simplify.
  fcf_spec_ret.
Qed. 

Theorem Gi_normal_prf_eq_compspec_ez_ : forall (k1 k2 v : Bvector eta),
    (* i <= length l -> *)
   comp_spec
     (fun (x : list (list (Bvector eta)) * (nat * KV))
        (y : list (list (Bvector eta)) * (nat * KV) * unit) =>
      fst x = fst3 y)
     (oracleMap (pair_EqDec nat_EqDec eqDecState) (list_EqDec eqdbv)
        (Oi_prg 1) (O, (k1, v)) (1::2::1::nil) )
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' 1) 
         (O, (k2, v)) (1::2::1::nil) ) unit unit_EqDec
        (f_oracle f eqdbv k1) tt).
(* expect RB PRF PRF *)
Proof.
  intros.
  unfold oracleMap.
  simplify.
  unfold GenUpdate_rb_intermediate.
  unfold Gen_loop_rb.
  simplify.
  comp_skip. admit. admit.
  simplify.
  fcf_spec_ret.
Qed.


(* easier version: hardcoded l and i *)
(* case i = 2, n = 3 -- pretty general *)
Theorem Gi_normal_prf_eq_compspec_ez : forall (k1 k2 v : Bvector eta),
    (* i <= length l -> *)
   comp_spec
     (fun (x : list (list (Bvector eta)) * (nat * KV))
        (y : list (list (Bvector eta)) * (nat * KV) * unit) =>
      fst x = fst3 y)
     (oracleMap (pair_EqDec nat_EqDec eqDecState) (list_EqDec eqdbv)
        (Oi_prg 2) (O, (k1, v)) (1::1::1::nil) )
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' 2) 
         (O, (k2, v)) (1::1::1::nil) ) unit unit_EqDec
        (f_oracle f eqdbv k1) tt).
Proof.
  intros.
  unfold oracleMap.
  simplify.
  unfold GenUpdate_rb_intermediate.
  unfold Gen_loop_rb.
  simplify.
  comp_skip. admit. admit.
  simplify.

  unfold GenUpdate_rb_intermediate.
  unfold Gen_loop_rb.
  simplify.
  comp_skip. admit. admit.
  simplify.

  fcf_spec_ret.
Qed.
*)

(* TODO 4/8/16

- state and admit the theorems below, and see if i can use them to QED the more general theorem

- prove a more general theorem relating each individual oracle? <-- numBlocks
   - GenUpdate_rb_intermediate vs. GenUpdate_rb_intermediate_oc
   - GenUpdate_noV vs GenUpdate_noV_oc
   - GenUpdate vs. GenUpdate_oc (with PRF oracle) and GenUpdate_PRF?
   (given the same internal state) <--- this should be a separate induction on numBlocks
- prove a more general theorem relating oracleMap and oracleCompMap_inner?
- prove a more general theorem relating each oracle (Oi_prg and Oi_oc')? <-- i, nc
   - this should be parametrized by i and numCalls

- this is still not enough to reason about the key changes? 
- could i even reuse these lemmas in the final theorem? it depends on numCalls
   - how would i reuse them? 

- also, how does this theorem relate to other ones? e.g. Gi_rb_eq_normal is similar, can I reuse this? *)

(* specific case of Gi_normal_prf_eq: i = 0, so only the PRF oracle is used *)
Theorem Gi_normal_prf_eq_compspec_i0 :
  forall (k1 v : Bvector eta) (calls : nat) l init,
    (* i <= length l -> *)
    calls > 0 ->                (* not the first call (which is special) *)
   comp_spec
     (fun (x : list (list (Bvector eta)) * (nat * KV))
        (y : list (list (Bvector eta)) * (nat * KV) * unit) =>
      fst x = fst3 y)
     (* (oracleMap (pair_EqDec nat_EqDec eqDecState) (list_EqDec eqdbv) *)
     (*    (Oi_prg O) (calls, (k1, v)) l) *)
     (compFold
        (pair_EqDec (list_EqDec (list_EqDec eqdbv))
           (pair_EqDec nat_EqDec eqDecState))
        (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ Oi_prg 0 s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (init, (calls, (k1, v))) l)

     ([acc', state'] <-$2 ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' O) 
         (calls, (k1, v)) l) unit unit_EqDec 
        (f_oracle f eqdbv k1) tt);
      [bits, nkv] <-2 acc';
      ret (init ++ bits, nkv, state')).
Proof.
  intros. revert k1 v calls H init.
  clear numCalls H_numCalls blocksPerCall.
  (* unfold oracleMap. *) (* need to start compFold with general acc *)
  rename l into lst.
  induction lst as [ | HEAD TAIL]; intros; simplify.

  * fcf_spec_ret. simpl. rewrite app_nil_r. reflexivity.
    (* Print oracleCompMap_inner. (* how does this compare to compFold? *) *)
  *
    destruct calls. omega.
    simpl.

    (*     fcf_skip.

    eapply comp_spec_eq_trans.
    eapply IHlsa.
    fcf_inline_first. *)

    (* fcf_skip. admit. admit. *)
    (* instantiate (1 := (fun x y => fst x = fst3 y)). *)
    (* simplify. *)
    (* fcf_spec_ret. *)

    Print Ltac simplify.

    (* fcf_inline_first. *)
    (* fcf_skip. admit. admit. *)

    (* unfold Gen_loop. *)
    (* destruct HEAD. *)
    (* simpl. *)
    (* simplify. *)
    (* Focus 2. *)
    (* simplify. *)
    simplify.
    
    eapply comp_spec_eq_trans_r.
    eapply IHTAIL.
    omega.

    fcf_skip_eq.
    admit. admit.

    (* TODO: because # calls = 2 and i = 0, the oracle is never used again, so it doesn't matter that the keys are different. induct on TAIL *)
    (* TODO: add back the first call *)
    (* TODO split this out / generalize it *)
    (* i think oracle irrelevance might help here? *)
    admit.

    simplify.
    fcf_spec_ret.
    rewrite <- app_assoc.
    f_equal.
Qed.

(* specific case of Gi_normal_prf_eq: i = length l, so only the RB oracle is used (if `i` were `length l - 1`, then we'd use the provided oracle on the last call) *)
Theorem Gi_normal_prf_eq_compspec_imax :
  forall (k1 v : Bvector eta) (i calls : nat) l init,
    (* i <= length l -> *)
    calls > 0 ->                (* not the first call (which is special) *)
    i = length l ->
   comp_spec
     (fun (x : list (list (Bvector eta)) * (nat * KV))
        (y : list (list (Bvector eta)) * (nat * KV) * unit) =>
      fst x = fst3 y)
     (* (oracleMap (pair_EqDec nat_EqDec eqDecState) (list_EqDec eqdbv) *)
     (*    (Oi_prg O) (calls, (k1, v)) l) *)
     (compFold
        (pair_EqDec (list_EqDec (list_EqDec eqdbv))
           (pair_EqDec nat_EqDec eqDecState))
        (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ Oi_prg i s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (init, (calls, (k1, v))) l)

     ([acc', state'] <-$2 ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (calls, (k1, v)) l) unit unit_EqDec 
        (f_oracle f eqdbv k1) tt);
      [bits, nkv] <-2 acc';
      ret (init ++ bits, nkv, state')).
Proof.

Admitted.
(* The two lemmas above are for practice purposes; don't need to prove them *)

(* folding on an acc that appends two lists = fold on the first list, use result as acc in fold on second list *)
Lemma fold_app_2 : forall (A0 B : Set) (eqd : EqDec A0) (c : A0 -> B -> Comp A0)
                          (ls1 ls2 : list B) (init0 x : A0) (res : A0),
    comp_spec eq (compFold eqd c init0 (ls1 ++ ls2))
              (init' <-$ compFold eqd c init0 ls1; compFold eqd c init' ls2).
Proof.
  intros.
  revert c ls2 init0 x res; induction ls1 as [| x1 xs1]; intros.
  - simpl. simplify. fcf_reflexivity.
  - simplify.
    fcf_skip_eq.
Qed.

Print oracleCompMap_inner. (* it doesn't use an init, and the oracle state is tt), so the ++ could just be separated? oh we also have to consider (Oi_oc' i) and calls.... yea if the oracle is PRF then everything is stateless? no doesn't the (k,v) change for the PRF (after RB RB PRF PRF...) then can we use that (the (k,v)) as the init? this might be independent of `calls` too. *)

(* similar app theorem about oracleCompMap_inner *)
(* oracleCompMap_inner (D R OracleIn OracleOut : Set) *)
(*                        (e1 : EqDec (list R * (nat * KV))) *)
(*                        (e2 : EqDec (list R)) *)
(*                        (oracleComp : nat * KV -> *)
(*                                      D -> *)
(*                                      OracleComp OracleIn OracleOut *)
(*                                        (R * (nat * KV)))  *)
(*                        (state : nat * KV) (inputs : list D) {struct inputs} : *)
(*  OracleComp OracleIn OracleOut (list R * (nat * KV)) := *)

(* is there some way i can have calls incremented, going into the second computation? *)
(* well it does say "state1" in the second one... what's the type of that? (calls, (k,v))
 should that automatically increment it? and if it did, would that fix anything? and it outputs state2 at the end *)
Lemma oracleCompMap_fold_app :
  forall
    (ls1 ls2 : list nat) (calls i : nat) (k1 k2 v : Bvector eta) (tt : unit),
    comp_spec eq
              (* (compFold eqd c init0 (ls1 ++ ls2)) *)
              (* (init' <-$ compFold eqd c init0 ls1; compFold eqd c init' ls2). *)
              (* tt is the state for the oracle (none) *)
              (* calls is the actual acc? *)
              (* ugh this doesn't take an acc does it. it starts from nil *)
              (* if i change the type what else will it break? *)
              ((oracleCompMap_inner
                  (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                              (pair_EqDec nat_EqDec eqDecState))
                  (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
                  (calls, (k2, v)) (ls1 ++ ls2)) unit unit_EqDec
                                                (f_oracle f eqdbv k1) tt)
              ([res1, _] <-$2 (oracleCompMap_inner
                                 (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                             (pair_EqDec nat_EqDec eqDecState))
                                 (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
                                 (calls, (k2, v)) ls1) unit unit_EqDec
                         (f_oracle f eqdbv k1) tt;
               [bits1, state1] <-2 res1;
               [res2, _] <-$2 (oracleCompMap_inner
                                 (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                             (pair_EqDec nat_EqDec eqDecState))
                                 (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
                                 state1 ls2) unit unit_EqDec
                         (f_oracle f eqdbv k1) tt;
               [bits2, state2] <-2 res2;
               ret (bits1 ++ bits2, state2, tt) ).
Proof.
  intros.
  
(* TODO prove this, but see if we can finish this proof using it + the ind hyp first *)
Admitted.

(*    comp_spec
     (fun (x : list (Bvector eta) * (nat * KV))
        (y : list (Bvector eta) * (nat * KV) * unit) => 
      fst x = fst3 y) (Oi_prg i (a0, b0) a)
     ((Oi_oc' i p a) unit unit_EqDec (f_oracle f eqdbv k1) tt) *)

(* problem: if they start with different keys, they may or may not be equal depending on what i, i', and n are? or maybe it doesn't matter??
wait but we need f's k1 to be the same as Oi_prg's k???

if we're doing PRF *)
(* what are i, calls, a y... *)
Lemma Oi_prg_Oi_oc_eq : forall (i calls numBlocks : nat)
                               (k1 k2 v : Bvector eta) (tt : unit),
   comp_spec
     (fun (x : list (Bvector eta) * (nat * KV))
        (y : list (Bvector eta) * (nat * KV) * unit) => 
      outputAndKVeq x y) (Oi_prg i (calls, (k1, v)) numBlocks)
     ((Oi_oc' i (calls, (k2, v)) numBlocks) unit unit_EqDec
        (f_oracle f eqdbv k1) tt).
Proof.
  intros.

Admitted.

Lemma multiple_skip_test : 
  comp_spec (fun a b => fst a = b /\ snd a = b)
            (x <-$ {0,1}^eta; y <-$ {0,1}^eta; ret (x,y))
            (x <-$ {0,1}^eta; ret x).
Proof.
  (* i can prove each of these individually, why can't i do it together? *)
  fcf_skip. admit. admit. admit.
  fcf_irr_l.
  fcf_spec_ret.
  simpl.
  (* SearchAbout getSupport. *)
  Print getSupport.
  Print getAllBvectors.

(* can I use H0 and H2 to reason about this? *)
(* can I add another sampling line *)
(* can I somehow phrase / reason about this probabilistically *)
(* even if I can prove this probabilistically, how do I get it to apply to the more complicated Instantiates below? *)
(* intuitively they should be indistinguishable right? *)
(* PRHL doesn't satisfy the conjunction rule *)
Admitted.

          (* 0 calls -> keys linked but not equal *)
          (* one call -> if RB then keys don't change so still linked,
if PRF (for the first time? or any PRF?) then both do (k' <- f k (to_list v'' ++ zeroes)) so since they had the same v, they should have the SAME key (which is stronger than "keys linked) 
but not necessarily *f*'s key *)
          (* induction? (SEPARATE induction?) for each call, keys linked, so at the end they remain linked? (call 1 -> last call in list: precondition -> postcondition)

RB -> RB: linked keys -> linked keys
RB -> PRF1: linked keys -> same keys
RB -> PRF: linked keys -> passed through PRF1 (same keys) -> same keys (??!)
PRF -> PRF: same keys -> same keys
other cases: impossible *)
          (* here: 
RB -> RB -> RB: linked keys -> linked keys -> linked keys
RB -> PRF1 -> PRF: linked keys -> same keys -> same keys
RB -> PRF -> PRF: linked keys -> passed through PRF1 (same keys) -> same keys -> same keys
PRF -> PRF -> PRF: same keys -> same keys -> same keys
other cases: impossible *)
          (* can i just get rid of the second oracleCompMap key? that would solve everything. i mean i only ever use RB, RF, and PRF as oracles. well RB requires that the PRFs afterward have a key *)
          (* i could probably specify this with a really elaborate postcondition and extreme casework *)
          (* so how do i state/prove this? what should the postcondition be? how do i deal with the list (and it passing thru PRF1)? *)
(* for 1st call: (f's key is k_f, k_prg' and k_oc' are output keys, k_prg and k_oc are input)
reintroduce `calls` as var, H: calls = 0?
maybe casework on l first, then i? not sure

(casework on i)
(RB)  calls = 0 /\ i > 0 -> k_prg' = k_f /\ k_oc' = k_oc
(PRF) calls = 0 /\ i = 0 -> k_prg' = k_oc' 
(I mean you could just compute this and get that both keys are f k (v_2||0), list is harder)

/\ for list: (callsL := length l, NOT S (length l))
(or should i prove this comp_spec separately? conjunction rule doesn't hold though)

(more casework on i and callsL (length l))
doesn't encode 1st call? well we should already have the above as a precondition (hypothesis)
(RB -> RB)   calls = callsL /\ callsL < i -> k_prg' = k_f /\ k_oc' = k_oc
(RB -> PRF1) calls = callsL /\ callsL = i -> k_prg' = k_oc' (by a SEPARATE induction?)
(RB -> PRF)  calls = callsL /\ callsL > i -> k_prg' = k_oc' (by a SEPARATE induction?)
(PRF -> PRF) calls = callsL /\ i = 0? -> k_prg' = k_oc'

/\ for call afterward: (callsL' := 1 + length l)
(no more casework needed, we have as hypotheses the postconditions above)
... and we need to prove what postcondition?!
(RB -> RB -> RB)    calls = callsL' /\ callsL' < i // can prove k_prg' = k_f /\ k_oc' = k_oc, so it's the same as above
(RB -> PRF1 -> PRF) calls = callsL' /\ callsL' = i // can prove k_prg' = k_oc' (not same as k_prg tho)
(RB -> PRF -> PRF)  calls = callsL' /\ callsL' > i // can prove k_prg' = k_oc'
(PRF -> PRF -> PRF) calls = callsL' /\ i = 0 // can prove k_prg' = k_oc'

^ ^ for above, add that the outputs are equal, and the v are equal
need to figure out what exactly the postcondition is (needs to be given abt list, and provable here) and what about the first call? maybe that's a subcase of this. actually it does look like a subcase.

postcondition: prove it holds on base case: OK
given that it holds on (x :: rev rev_xs'),
show it holds on (x :: rev rev_xs' ++ rev_x' :: nil)
  that is, given that the postcondition is true after (x :: rev rev_xs'),
  show that it is still true after rev_x'. it seems to be true, actually! i proved it above
how to deal with -> PRF1 -> PRF? *)

(* new version of theorem below with more complex postcondition *)
Definition bitsCallsKVeq {A B : Type} (i : nat) (l : list B) (k_f k_oc : Bvector eta)
           (x : A * (nat * KV)) (y : A * (nat * KV) * unit) :=
  let (bits_prg, state_prg) := x in
  let (calls_prg, kv_prg) := state_prg in
  let (k_prg', v_prg) := kv_prg in
  let (bits_oc, state_oc) := fst y in
  let (calls_oc, kv_oc) := state_oc in
  let (k_oc', v_oc) := kv_oc in
  (* bits, calls, V straightforward *)
  (* OLD CALLS + len l *)
  bits_prg = bits_oc /\ calls_prg = length l /\ calls_oc = length l /\ v_prg = v_oc
  (* k is more complex, also note calls_prg = calls_oc *)
  /\ (calls_prg < i -> k_prg' = k_f /\ k_oc = k_oc)
  /\ (calls_prg = i -> k_prg' = k_oc')
  /\ (calls_prg > i -> k_prg' = k_oc')
  /\ (i = 0 -> k_prg' = k_oc'). (* combine the three into one hypothesis? *)

Definition bitsCallsKVeq_RB {A B : Type} (l1 l2 l : list B) (i : nat) (k_f k_oc : Bvector eta)
           (x : A * (nat * KV)) (y : A * (nat * KV) * unit) :=
  let (bits_prg, state_prg) := x in
  let (calls_prg, kv_prg) := state_prg in
  let (k_prg', v_prg) := kv_prg in
  let (bits_oc, state_oc) := fst y in
  let (calls_oc, kv_oc) := state_oc in
  let (k_oc', v_oc) := kv_oc in
  (* bits, calls, V straightforward *)
  (* OLD CALLS + len l *)
  bits_prg = bits_oc /\ calls_prg = calls_oc
  /\ v_prg = v_oc
  /\ calls_prg <= i /\ k_prg' = k_f /\ k_oc = k_oc'
  /\ l = l1 ++ l2 /\ length l1 = calls_prg /\ i < length l2.

(* new postcondition *)
Definition bitsVEq {A : Type} 
           (x : A * (nat * KV)) (y : A * (nat * KV) * unit) :=
  let (bits_x, state_x) := x in
  let (calls_x, kv_x) := state_x in
  let (k_x, v_x) := kv_x in

  let (bits_y, state_y) := fst y in
  let (calls_y, kv_y) := state_y in
  let (k_y, v_y) := kv_y in
  (* no statement about keys being equal for now *)
  bits_x = bits_y /\ v_x = v_y /\ calls_x = calls_y.

Ltac breakdown x := simpl in x; decompose [and] x; clear x; subst.

Theorem Gi_normal_prf_eq_compspec_post3 :
  forall (l : list nat) (i calls : nat) (k1 k2 v : Bvector eta) init,
    calls <= i ->
    (* calls < length l -> *)
    (* i < length l -> *)

    comp_spec
      (fun (x : list (list (Bvector eta)) * (nat * KV))
           (y : list (list (Bvector eta)) * (nat * KV) * unit) =>
         bitsVEq x y)

      (compFold
        (pair_EqDec (list_EqDec (list_EqDec eqdbv))
           (pair_EqDec nat_EqDec eqDecState))
        (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ Oi_prg i s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (init, (calls, (k1, v))) l)
      (* should calls and init be linked? *)

     ([acc', state'] <-$2 ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (calls, (k2, v)) l) unit unit_EqDec 
        (f_oracle f eqdbv k1) tt);
      [bits, nkv] <-2 acc';
      ret (init ++ bits, nkv, state')).
Proof.
  induction l as [ | x xs]; intros.

  - simpl in *.
    simplify.
    fcf_spec_ret.
    simpl.
    repeat (split; auto).
    rewrite app_nil_r. reflexivity.

  -                             (* l = x :: xs *)
    assert (H_ilen : calls < i \/ calls = i) by omega.
    destruct H_ilen.
    clear H.

    (* calls < i *)
    + Opaque Oi_prg. Opaque Oi_oc'.
      unfold oracleMap.
      simplify.
      fcf_skip. admit. admit.
      (* strengthen postcondition so we can prove calls < i -> S calls <= i to apply IHxs *)
      (* also strengthen it again because if calls < i then the keys must still be the same *)
      instantiate (1 := (fun c d => bitsVEq c d
                                    /\ fst (snd c) = S calls /\ fst (snd (fst d)) = S calls
                                    /\ fst (snd (snd c)) = k1
                                    /\ fst (snd (snd (fst d))) = k2)).
      (* includes calls *)
      (* one call with linked keys TODO *)
      { admit. }

      (* use IH *)
      { simpl in H2. destruct b0. destruct b. destruct p. destruct p. destruct k. simpl in *.
        breakdown H2. 
        simplify.

        eapply comp_spec_eq_trans_r.
        eapply IHxs; omega. 

        (* now prove oracleCompMap_inner's eq *)
        { fcf_skip_eq. admit. admit.
          simplify.
          instantiate (1 := k2).
          destruct u.
          fcf_reflexivity.
          simplify.
          fcf_spec_ret. rewrite <- app_assoc. f_equal.
        }
      } 
    
    (* calls = i *)
  + clear IHxs.

    Lemma Gi_normal_prf_eq_calls_eq_i :
      forall (l : list nat) (i calls : nat) (k1 k2 v : Bvector eta) init,
        calls = i ->
        comp_spec
          (fun (c : list (list (Bvector eta)) * (nat * KV))
               (d : list (list (Bvector eta)) * (nat * KV) * unit) => 
             bitsVEq c d)
          (compFold
             (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                         (pair_EqDec nat_EqDec eqDecState))
             (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
                [rs, s]<-2 acc;
              z <-$ Oi_prg i s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
             (init, (calls, (k1, v))) l)
          (z <-$
             (oracleCompMap_inner
                (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                            (pair_EqDec nat_EqDec eqDecState))
                (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
                (calls, (k2, v)) l) unit unit_EqDec 
             (f_oracle f eqdbv k1) tt;
           [bits, nkv, state']<-3 z; ret (init ++ bits, nkv, state')).
    Proof.
      destruct l as [ | x xs]; intros.

      - simplify. fcf_spec_ret. simpl. repeat (split; auto).
        rewrite app_nil_r; reflexivity.
      -
        simplify.
        fcf_skip. admit. admit.
        instantiate (1 := (fun c d => bitsVEq c d
                                      /\ fst (snd c) = S calls /\ fst (snd (fst d)) = S calls
                                      (* keys become equal afterward on call i *)
                                      /\ fst (snd (snd c)) = fst (snd (snd (fst d))))).
        (* 1 call *)
        {
          Transparent Oi_prg. Transparent Oi_oc'.
          unfold Oi_prg. unfold Oi_oc'.
          simplify.
          (* casework on `calls = i` and `calls > i` *)
          admit. }

        (* rest of calls -- induct on the new list *)
        { simplify. simpl in *. destruct b0. destruct p. destruct k. simpl in *. breakdown H2. 

          clear H1 H3 H0.
          rename b1 into k'. rename b2 into v'.
          remember (S i) as calls.
          assert (H_calls : calls > i) by omega.
          clear Heqcalls k2 v.
          revert x i k1 init l k' v' u calls H_calls.
          induction xs as [ | x' xs']; intros.

          (* xs = nil *)
          + simplify. fcf_spec_ret. simpl. repeat (split; auto).
          (* xs = x' :: xs', use IH *)
          + Opaque Oi_prg. Opaque Oi_oc'.
            simplify.
            fcf_skip. admit. admit.

            (* one call with calls > i (calls = S i) *)
            instantiate (1 := (fun c d => bitsVEq c d
                                          (* calls incremented by one *)
                                          /\ fst (snd c) = S (calls)
                                          /\ fst (snd (fst d)) = S (calls)
                                          (* keys equal *)
                                          /\ fst (snd (snd c)) = fst (snd (snd (fst d))))).
            { admit. }

            simpl in H2. destruct b0. destruct b. destruct p. destruct p. destruct k. simpl in *. breakdown H2.
            simplify.
          
            eapply comp_spec_eq_trans_r. 
            eapply H; omega.
            
            (* now prove oracleCompMap_inner's eq *)
            { instantiate (1 := k1). 
              fcf_skip_eq. admit. admit.
              simplify. fcf_spec_ret.
              f_equal. f_equal.
              rewrite <- app_cons_eq.
              reflexivity.
            }
        }
    Qed.

    apply Gi_normal_prf_eq_calls_eq_i; omega.
Qed.
        
      
      (* -------- *)
      (* induct on reverse *)
(*
      remember (rev l) as rev_l.
      assert (H_revl: rev (rev l) = l).
      { apply rev_involutive. }
      rewrite <- H_revl.
      rewrite <- Heqrev_l.
      clear Heqrev_l H_revl.
      revert i calls k1 k2 v H.

      induction rev_l as [ | rev_x' rev_l']; intros.

      - unfold oracleMap.
        simplify.
        fcf_spec_ret.
        simpl.
        repeat (split; auto).

      - simpl.
        unfold oracleMap.
        eapply comp_spec_eq_trans_l.
        apply fold_app_2. admit. admit.

        apply comp_spec_symm.
        eapply comp_spec_eq_trans_l.
        apply oracleCompMap_fold_app. (* is this strong enough? and fold_app_2? *)
        apply comp_spec_symm.

        fcf_skip. admit. admit.
        
        + apply IHrev_l'; auto.

        +
          simpl in H2. destruct b0. destruct b. repeat destruct p. destruct k. simpl in *.
          breakdown H2. subst.
          simplify.
          fcf_skip. admit. admit.

          Show Existentials.
          instantiate (1 := (fun c d => fst c = fst (fst d) /\ snd c = snd (fst d))).
    (* is this true? wait the keys are not linked... because...we don't have that postcondition on the IH. but we can add a more specific postcondition? do we need the calls stuff too? *)
          (* or, maybe i shouldn't induct on the reverse?? *)
          rename b2 into v'.
          

          admit.

          simpl in H4. breakdown H4. destruct b1. destruct p. simpl in *. subst.
          simplify.
          fcf_spec_ret. simpl. destruct b3. repeat (split; auto).
    Qed. *)

(* TODO: fix instantiations of bitsCallsKVeq below and fix postconditions
(where there is `repeat (split; try auto))` *)
Theorem Gi_normal_prf_eq_compspec_post2 :
  forall (l : list nat) (i calls : nat) (k1 k2 v : Bvector eta),
    calls <= i ->
    calls < length l ->
    i < length l ->
   comp_spec

     (fun (x : list (list (Bvector eta)) * (nat * KV))
        (y : list (list (Bvector eta)) * (nat * KV) * unit) =>
        bitsCallsVEq l calls i x y)

     (oracleMap (pair_EqDec nat_EqDec eqDecState) (list_EqDec eqdbv)
        (Oi_prg i) (calls, (k1, v)) l)

     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (calls, (k2, v)) l) unit unit_EqDec (* note: k's differ. we aren't using this one *)
        (f_oracle f eqdbv k1) tt).
Proof.
 (* TODO:
- understand (on paper) what it means to assert and prove IH vs add assumptions X
  - same as adding assumption -- just proving it inline vs. proving it when we apply thm
- understand the invariant: length l > i - calls
  - this is true because calls increases and i is fixed... but why do we need it?
  - becomes 
- understand the IH (precondition?) 
  - before an RB call, the initial bits and v are eq, and there are calls remaining
  - IH in theorem: ??

- just think about inducting on l (not its reverse) and what that means
- write out the base case and induction case 1, induction case 2
  - understand the ind cases
  - figure out if the 3 cases are true
- figure out new postcondition
- prove two cases with new postcondition *)

  (* induct on l (or l2?) start w calls < i, stop when calls = i (no longer true) *)
  intros.
  (* wait, here we're inducting on calls? *)
  (* induction calls as [ | calls']. *)

  pose (bits := @nil (list (Bvector eta))).
  assert (H_states : bitsCallsVEq l calls i (bits, (calls, (k1, v))) (bits, (calls, (k2, v)), tt)). {
    simpl.
    repeat (split; auto; try omega). 
  }
  clearbody bits.
  clear H0.
  (* what's this invariant? are we only using it for base case *)
  (* assert (Hlen : length l > i - calls). *)
  (* { omega. } *)
  clear H1.
  
  revert bits calls H H_states.
  (* calls increases as l decreases *)
  induction l as [ | x xs]; intros.

  - simpl in *.
    simplify.
    fcf_spec_ret.
    simpl.
    repeat (split; auto).
    (* base case is true if we don't change this postcondition, otherwise may need Hlen *)
    (* simpl in Hlen. *)
    (* omega. *)
  -
    (* IHxs : forall (bits : list (list (Bvector eta))) (calls : nat),
         calls <= i ->
given by H? confused. oh, the IH only applies when calls remains <= i. 
we need to do other reasoning when calls > i (or calls = i???)
well we assert (calls < i \/ calls = i... confused)

         bitsCallsVEq xs calls i (bits, (calls, (k1, v)))
           (bits, (calls, (k2, v)), tt) ->
this holds on what?

         length xs > i - calls ->
not sure why we need this. given `length x:: xs > i - calls` = `S (length xs) > i - calls`, that... doesn't seem to be true? idt we need this?
length xs + 1 > i - calls
calls <= i
-> length xs + 1 > i - calls >= 0

         comp_spec
           (fun (x0 : list (list (Bvector eta)) * (nat * KV))
              (y : list (list (Bvector eta)) * (nat * KV) * unit) =>
            bitsCallsVEq xs calls i x0 y)
           (oracleMap (pair_EqDec nat_EqDec eqDecState) 
              (list_EqDec eqdbv) (Oi_prg i) (calls, (k1, v)) xs)
           ((oracleCompMap_inner
               (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                  (pair_EqDec nat_EqDec eqDecState))
               (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
               (calls, (k2, v)) xs) unit unit_EqDec 
              (f_oracle f eqdbv k1) tt) 
postcondition holds on xs

how to apply it to "want to prove postcondition holds on (x :: xs) w same starting state"

-----
  H_states : bitsCallsVEq (x :: xs) calls i (bits, (calls, (k1, v)))
               (bits, (calls, (k2, v)), tt) -- or
  H_states : bits = bits /\
             calls <= S (length xs) /\ calls <= S (length xs) /\ v = v
given: maybe this is instantiated wrong? bits and v eq (redundant), calls < ...
so this isn't very useful...
do we even need a precondition? it's implicitly stated in the theorem (input v eq, no bits)
but i could generalize it to (bits <-$ ...; ret (first_bits :: bits))

  H : calls <= i 
don't understand this, should it be true? is it analogous to `calls = 0` before?
do i even need this?

  Hlen : length (x :: xs) > i - calls
???     *)
    simpl in H_states.
    (* simpl in Hlen. *)
    decompose [and] H_states; clear H_states.
    clear H0 H1 H4.

    (* assert (H_ilen : length xs > i - calls \/ i - calls = length xs) by omega. *)
    assert (H_ilen : i > calls \/ i = calls) by omega.
    destruct H_ilen.

  +
    assert (bits': list (list (Bvector eta))) by admit.
    specialize (IHxs bits' (S calls)).
    (* bits should be returned by... *)

    assert (pre : bitsCallsVEq xs (S calls) i (bits', (S calls, (k1, v)))
           (bits', (S calls, (k2, v)), tt)). admit.
    admit.

  +
    clear IHxs.
    (* this is true! i = calls, and the keys are linked *)
    (* what happened above? i'm not sure *)
    (* precondition? invariant? ?? *)
    (* do a separate induction? this should really be a separate theorem that we can apply here. *)
    admit.

Admitted.

(* old proof attempts *)
(*  destruct l as [ | x xs].
  - 
    simpl in *. omega.
  - clear H_numCalls.
    remember (rev xs) as rev_xs.
    assert (H_revxs: rev (rev xs) = xs).
    { apply rev_involutive. }
    rewrite <- H_revxs.
    rewrite <- Heqrev_xs.
    clear Heqrev_xs H_revxs H.
    revert i k1 k2 v.

    induction rev_xs as [ | rev_x' rev_xs']; intros.

    (* list is `x :: rev nil` *)
    +
      Opaque oracleMap. Opaque oracleCompMap_inner.
      simpl.
      Transparent oracleMap. Transparent oracleCompMap_inner.
      Opaque Oi_prg. Opaque Oi_oc'.
      unfold oracleMap.
      simpl.
      fcf_inline_first.
      fcf_skip. admit. admit.
      instantiate (1 := (fun x' y' => bitsCallsKVeq i (x::nil) k1 k2 x' y')).
      (* check these are instantiated properly *)

      *
        Transparent Oi_prg. Transparent Oi_oc'.
        unfold Oi_prg. unfold Oi_oc'.

        (* for calls = 0 -- fixes the base case? *)
        simpl.
        destruct (lt_dec 0 i).

        { unfold GenUpdate_rb_intermediate. simplify. fcf_skip. admit. admit. simplify.
          fcf_spec_ret. simpl. (* keys not equal *)
          repeat (split; try auto); admit.
        }
        { simpl.
          fcf_inline_first.
          fcf_skip. admit. admit.
          instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd (snd x) = snd (fst y))).
          admit.

          simpl in H1. destruct H1. destruct b0. destruct p. destruct b. simpl in *. subst.
          simplify. fcf_spec_ret. simpl.
          repeat (split; try auto); admit.
          (* i didn't specify here that the keys would be equal, so the postcondition doesn't show it *)
        }
      * (* finish it off *)
        simpl in H1. destruct b. simpl in H1. destruct b0. destruct p. destruct p. destruct k.
        Transparent Oi_prg. Transparent Oi_oc'.
        destruct H1. destruct H2. destruct H3. subst.
        (* write a better postcondition or an ltac TODO *)
        simplify. fcf_spec_ret. simpl.
        repeat (split; try auto).

    (* list is `x :: rev (rev_x' :: rev_xs')` *)
    + 
      Opaque oracleMap. Opaque oracleCompMap_inner.
      simpl.
      Transparent oracleMap. Transparent oracleCompMap_inner.

      (* ind hyp holds on (x :: rev rev_xs') so DON'T simpl x out, rewrite w/ fold ++ lemma *)
      rewrite app_comm_cons.
      remember (x :: rev rev_xs') as nonempty.

      unfold oracleMap.
      eapply comp_spec_eq_trans_l.
      apply fold_app_2. admit. admit.

      apply comp_spec_symm.
      eapply comp_spec_eq_trans_l.
      apply oracleCompMap_fold_app. (* is this strong enough? and fold_app_2? *)
      apply comp_spec_symm.

      fcf_skip. admit. admit.

      (* induction hypothesis *)
      * apply IHrev_xs'.
        (* here calls is 0... oh that's right, it's the head of the list so calls remains 0! *)
      *
        simpl in H1. destruct b. simpl in H1. destruct b0. destruct p. destruct p. destruct k.
        destruct H1. destruct H2. destruct H3. subst.
        rewrite rev_length.
        (* postcondition: note that bits and v are the same, and calls is (S (length rev_xs')) *)
        (* now, does calls = 0 -> calls = S (length rev_xs') fix the ind. case?? *)
        (* we may need to strengthen the postcondition to fix the ind. case *)
        Opaque Oi_prg. Opaque Oi_oc'.
        simplify.

        (* so the postcondition seems to be provable at least for calls inc *)
        fcf_skip. admit. admit.
        (* what should this be? should the list change? *)
        (* is this true? admitted the two one-calls (Oi relating) *)

        (* note instantiation with b1 *)
        instantiate (1 := (fun x' y' => bitsCallsKVeq i (x :: rev rev_xs' ++ rev_x' :: nil) k1 b1 x' y')).
        {
          rename b2 into v'.
          Transparent Oi_prg. Transparent Oi_oc'.
          unfold Oi_prg. unfold Oi_oc'.

          remember (S (length rev_xs')) as callsSoFar.
          assert (beq_dec : beq_nat callsSoFar 0 = true \/ ~ beq_nat callsSoFar 0 = true).
          { destruct (beq_nat callsSoFar 0); auto. }
          destruct beq_dec.
          (* callsSoFar > 0, so no GenUpdate_noV *)
          subst. simpl in H1. inversion H1.

          apply not_true_is_false in H1.
          rewrite H1.

          subst.
          admit.
        }
        { simplify.
          fcf_spec_ret.
          simpl in *.
          destruct b4, p. destruct k. destruct H8. destruct H8. destruct H9. destruct H10. destruct H11.

          repeat (split; subst; try auto).
          (* ??? *)
          admit. 
        }
Qed.
Transparent oracleMap.
Transparent oracleCompMap_inner.
Transparent Oi_prg. Transparent Oi_oc'.
*)

(* version of theorem below with different postcondition *)
(* other ideas:
- need to make the theorem somehow true for the base case
  - is it true if calls starts < i? yes but i can't prove that inductively holds?
- or, different strategy: stitch together what i've already proved (all RBs, PRF oracle use, then all PRFs) because each case is inductive. but then i have to somehow prove that equivalent to this which seems even harder. and there are many edge cases e.g. if i = 0, no RBs happen, or for some i, no oracle is used, or no PRFs happen

so i have to prove EACH of them equivalent to some intermediate expression?
what expression? and what postcondition? and does this even fix the base case problem?
as what function of `calls`, `length l`, and `i`
does this fix the inductive problem if true/provable?
is it provable?

comp_spec ?

let (firsthalfl, secondhalf) := (firstn (i-calls) l, sndn (length l - i) l) in
compMap (i - calls) RB firsthalfl ++ oracleMap (length l - i) PRF (k,v) secondhalfl

(note if calls >= i then the result is simply 0)
need to add another hypothesis that i <= length l?

i just don't see why you would do this, it looks worse than the oracleMap expression we originaly wanted to prove equivalence to

     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (calls, (k2, v)) l) unit unit_EqDec (* note: k's differ. we aren't using this one *)
        (f_oracle f eqdbv k1) tt).

      and with

     (oracleMap (pair_EqDec nat_EqDec eqDecState) (list_EqDec eqdbv)
        (Oi_prg i) (calls, (k1, v)) l)

- still can't make all the keys the same?
- maybe try calls = 0 then prove general "calls" = calls 0 with different n and i? how to prove that though? induction?
- more complicated/specific ind invariant: if calls = 0 then it returns ... else if calls > i then ... else ... and afterward calls = ... 
  still a postcondition might help for the inductive case, but won't work for the base case
- i'm fairly sure the top-level theorem is true though!! *)

Theorem Gi_normal_prf_eq_compspec_post :
  forall (l : list nat) (i : nat) (k1 k2 v : Bvector eta),
    length l > 0 ->
   comp_spec
     (fun (x : list (list (Bvector eta)) * (nat * KV))
        (y : list (list (Bvector eta)) * (nat * KV) * unit) =>
        bitsCallsVEq l x y)

     (oracleMap (pair_EqDec nat_EqDec eqDecState) (list_EqDec eqdbv)
        (Oi_prg i) (0, (k1, v)) l)
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (0, (k2, v)) l) unit unit_EqDec (* note: k's differ. we aren't using this one *)
        (f_oracle f eqdbv k1) tt).
Proof.
  intros.
  
  destruct l as [ | x xs].
  - 
    simpl in *. omega.
  - clear H_numCalls.
    remember (rev xs) as rev_xs.
    assert (H_revxs: rev (rev xs) = xs).
    { apply rev_involutive. }
    rewrite <- H_revxs.
    rewrite <- Heqrev_xs.
    clear Heqrev_xs H_revxs H.
    revert i k1 k2 v.

    induction rev_xs as [ | rev_x' rev_xs']; intros.

    (* list is `x :: rev nil` *)
    +
      Opaque oracleMap. Opaque oracleCompMap_inner.
      simpl.
      Transparent oracleMap. Transparent oracleCompMap_inner.
      Opaque Oi_prg. Opaque Oi_oc'.
      unfold oracleMap.
      simpl.
      fcf_inline_first.
      fcf_skip. admit. admit.
      instantiate (1 := (fun x' y' => bitsCallsVEq (x::nil) x' y')).

      *
        (* prove postcondition relating Oi_prg and Oi_oc' *)
        (* TODO: start w/ precondition on whether calls < i and then as the list grows, destruct/casework on whether it remains so?? like 2+ more cases... *)
        (* calls < i -> len rev_xs > ... -> calls > i? *)
        (* but the theorem is just false for certain base cases (calls > i) -- but those aren't true initially since calls starts at 0, maybe generalize to `calls <= numCalls - length l? idk. the original invariant is true, but we need to include i somehow... *)
        (* note: we can make the RB case true by simply rand sampling & replacing both keys? *)
        (* wait i'm confused, does RB replace the key or retain the original key?? if it retains the original key, we should keep the link between k1 in Oi_prg and in f_oracle? also maybe we shouldn't induct on the list? case "len list = i" and so on are the only ones that matter? *)
        (* in fact GenUpdate_rb_intermediate does not update k **OR** v. you can do whatever you want for that. maybe i should prove in the fold lemmas that the key is linked (if ...? casework?). *)
        (* STILL false for keys linked AND calls > i, in base case *)
        (* what if i don't induct on the reverse? lol *)

        Transparent Oi_prg. Transparent Oi_oc'.
        unfold Oi_prg. unfold Oi_oc'.

        (* for calls = 0 -- fixes the base case, i think! *)
        simpl.
        destruct (lt_dec 0 i).

        { unfold GenUpdate_rb_intermediate. simplify. fcf_skip. admit. admit. simplify.
          fcf_spec_ret. simpl. auto. (* keys not equal *) }
        { simpl.
          fcf_inline_first.
          fcf_skip. admit. admit.
          instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd (snd x) = snd (fst y))).
          admit.

          simpl in H1. destruct H1. destruct b0. destruct p. destruct b. simpl in *. subst.
          simplify. fcf_spec_ret. simpl. auto.
          (* well i didn't specify here that the keys would be equal, so the postcondition doesn't show it *)
        }
      * (* finish it off *)
        simpl in H1. destruct b. simpl in H1. destruct b0. destruct p. destruct p. destruct k.
        Transparent Oi_prg. Transparent Oi_oc'.
        destruct H1. destruct H2. destruct H3. subst.
        (* write a better postcondition or an ltac TODO *)
        simplify. fcf_spec_ret. simpl. auto.

    (* list is `x :: rev (rev_x' :: rev_xs')` *)
    + 
      Opaque oracleMap. Opaque oracleCompMap_inner.
      simpl.
      Transparent oracleMap. Transparent oracleCompMap_inner.

      (* ind hyp holds on (x :: rev rev_xs') so DON'T simpl x out, rewrite w/ fold ++ lemma *)
      rewrite app_comm_cons.
      remember (x :: rev rev_xs') as nonempty.

      unfold oracleMap.
      eapply comp_spec_eq_trans_l.
      apply fold_app_2. admit. admit.

      apply comp_spec_symm.
      eapply comp_spec_eq_trans_l.
      apply oracleCompMap_fold_app. (* is this strong enough? and fold_app_2? *)
      apply comp_spec_symm.

      fcf_skip. admit. admit.

      (* induction hypothesis *)
      * apply IHrev_xs'.
        (* here calls is 0... oh that's right, it's the head of the list so calls remains 0! *)
      *
        simpl in H1. destruct b. simpl in H1. destruct b0. destruct p. destruct p. destruct k.
        destruct H1. destruct H2. destruct H3. subst.
        rewrite rev_length.
        (* postcondition: note that bits and v are the same, and calls is (S (length rev_xs')) *)
        (* now, does calls = 0 -> calls = S (length rev_xs') fix the ind. case?? *)
        (* we may need to strengthen the postcondition to fix the ind. case *)
        Opaque Oi_prg. Opaque Oi_oc'.
        simplify.

        (* so the postcondition seems to be provable at least for calls inc *)
        fcf_skip. admit. admit.
        (* what should this be? should the list change? *)
        (* is this true? admitted the two one-calls (Oi relating) *)

        instantiate (1 := (fun x' y' => bitsCallsVEq (x :: rev rev_xs' ++ rev_x' :: nil) x' y')).
        {
          rename b2 into v'.
          (* is this strong enough? no? well maybe? i think i failed at linking the key with k1 *)
          (* depends now on whether callsSoFar > i... gotta think about casework again. should every case be triggered here? what about above? confused -- it should hold for ANY xs, right? meaning, take length >= 1, is the best you can do. but it doesn't give you any guarantees WRT i (besides that i <= length l) *)
          (* so i still don't know how to deal with `calls > i` case, and now that the `k` aren't linked, i still don't know how to deal with `calls = i`. why aren't the `k` linked here though? well cause the former one iterated a nonzero amt of times so it shouldn't be the same. TODO i'm missing something here... *)
          (* and might it work if i put the `calls` invariant back in? *)
          (* calls + length l = numCalls? *)
          Transparent Oi_prg. Transparent Oi_oc'.
          unfold Oi_prg. unfold Oi_oc'.

          (* casework on (lt_dec (S (length rev_xs'))) etc.? *)
          (* also a case isn't true? i should be able to prove k's eq after IH? postcondition? depende on length of rev_xs'... *)
          (* maybe i don't really understand what it is to induct on the reverse of a list *)
          (* one call happened, then some number n of calls happened *)
          (* casework on n and i *)
          (* it would be great if calls were 0 again!! *)
          remember (S (length rev_xs')) as callsSoFar.
          assert (beq_dec : beq_nat callsSoFar 0 = true \/ ~ beq_nat callsSoFar 0 = true).
          { destruct (beq_nat callsSoFar 0); auto. }
          destruct beq_dec.
          (* callsSoFar > 0, so no GenUpdate_noV *)
          subst. simpl in H1. inversion H1.

          apply not_true_is_false in H1.
          rewrite H1.

SearchAbout comp_spec.

          (* 0 calls -> keys linked but not equal *)
          (* one call -> if RB then keys don't change so still linked,
if PRF (for the first time? or any PRF?) then both do (k' <- f k (to_list v'' ++ zeroes)) so since they had the same v, they should have the SAME key (which is stronger than "keys linked) 
but not necessarily *f*'s key *)
          (* induction? (SEPARATE induction??) for each call, keys linked, so at the end they remain linked? (call 1 -> last call in list: precondition -> postcondition)

RB -> RB: linked keys -> linked keys
RB -> PRF1: linked keys -> same keys
RB -> PRF: linked keys -> passed through PRF1 (same keys) -> same keys (??!)
PRF -> PRF: same keys -> same keys
other cases: impossible *)
          (* here: 
RB -> RB -> RB: linked keys -> linked keys -> linked keys
RB -> PRF1 -> PRF: linked keys -> same keys -> same keys
RB -> PRF -> PRF: linked keys -> passed through PRF1 (same keys) -> same keys -> same keys
PRF -> PRF -> PRF: same keys -> same keys -> same keys
other cases: impossible *)
          (* can i just get rid of the second oracleCompMap key? that would solve everything. i mean i only ever use RB, RF, and PRF as oracles. well RB requires that the PRFs afterward have a key *)
          (* i could probably specify this with a really elaborate postcondition and extreme casework *)
          (* so... how do i state/prove this? what should the postcondition be? how do i deal with the list (and it passing thru PRF1)? *)
(* for 1st call: (f's key is k_f, k_prg' and k_oc' are output keys, k_prg and k_oc are input)
reintroduce `calls` as var, H: calls = 0?
maybe casework on l first, then i? idk

(casework on i)
(RB)  calls = 0 /\ i > 0 -> k_prg' = k_f /\ k_oc' = k_oc
(PRF) calls = 0 /\ i = 0 -> k_prg' = k_oc' 

(I mean you could just compute this and get that both keys are f k (v_2||0), list is harder)

/\ for list: (callsL := length l, NOT S (length l))
(or should i prove this comp_spec separately? conjunction rule doesn't hold though...

(more casework on i and callsL (length l))
doesn't encode 1st call? well we should already have the above as a precondition (hypothesis)
(RB -> RB)   calls = callsL /\ callsL < i -> k_prg' = k_f /\ k_oc' = k_oc
(RB -> PRF1) calls = callsL /\ callsL = i -> k_prg' = k_oc' (by a SEPARATE induction?)
(RB -> PRF)  calls = callsL /\ callsL > i -> k_prg' = k_oc' (by a SEPARATE induction?)
(PRF -> PRF) calls = callsL /\ i = 0? -> k_prg' = k_oc'

/\ for call afterward: (callsL' := 1 + length l)
(no more casework needed, we have as hypotheses the postconditions above)
... and we need to prove what postcondition?!
(RB -> RB -> RB)    calls = callsL' /\ callsL' < i // can prove k_prg' = k_f /\ k_oc' = k_oc, so it's the same as above
(RB -> PRF1 -> PRF) calls = callsL' /\ callsL' = i // can prove k_prg' = k_oc' (not same as k_prg tho)
(RB -> PRF -> PRF)  calls = callsL' /\ callsL' > i // can prove k_prg' = k_oc'
(PRF -> PRF -> PRF) calls = callsL' /\ i = 0 // can prove k_prg' = k_oc'

^ ^ for above, add that the outputs are equal, and the v are equal

need to figure out what exactly the postcondition is (needs to be given abt list, and provable here) and what about the first call? maybe that's a subcase of this. actually it does look like a subcase.

postcondition: prove it holds on base case: OK
given that it holds on (x :: rev rev_xs'),
show it holds on (x :: rev rev_xs' ++ rev_x' :: nil)
  that is, given that the postcondition is true after (x :: rev rev_xs'),
  show that it is still true after rev_x'. it seems to be true, actually! i proved it above!
how to deal with -> PRF1 -> PRF?

TODO email adam / ask lennart for help *)

          subst.
          

        }
        { simplify.
          fcf_spec_ret.
          simpl in *.
          destruct b3, p. destruct k. destruct H3. destruct H4. destruct H5.
          subst.
          repeat split.
        }
        
Qed.
Transparent oracleMap.
Transparent oracleCompMap_inner.
Transparent Oi_prg. Transparent Oi_oc'.

    (* actually is this true if calls starts at any number?? and for any i?
       what invariant could we add? *)
    (* i = 0 (all PRF, oracle used on call 0) ->
           calls starts at 0 -> as intended, should be true
           calls starts at c > 0 -> the oracle is no longer being used, and the input keys...
              are not equal... (k1 != k2) this is wrong TODO *)
    (* i = 1..n-1 (RB.. RB PRF .. PRF) ->
           calls < i -> the oracle hasn't been used yet, so the outputs (produced by RB) don't use the key, then when the oracle is used, the key overrides
           calls = i -> same reasoning for RB, and the oracle is used on this call & outputs a key that overrides
           calls > i -> again, the oracle is no longer being used, and the input keys are not equal for the PRF use
     *)
    (* i = n = length l (all RB) -> clearly true for all calls since oracle is never used and keys are never used *)

    (* so for a few cases above, the theorem is just not true *)
    (* so should we try calls <= i? no, not good inductive invariant *)
    (* or should we backtrack and try to fcf_skip the correct line... *)
    (* even if i could skip the correct line, would it be true? no, if the oracle is called and the key is not the same as Oi_prg's, the results are wrong *)
    (* i mean it would be nice if EVERYONE'S keys were the same. can i do that? is that even true?*)
    (* that's equivalent to the lemma above *)
Theorem Gi_normal_prf_eq_compspec :
  forall (l : list nat) (i : nat) (k1 k2 v : Bvector eta) (calls : nat),
    length l > 0 ->
    (* something like, calls + ? = length l? `i` doesn't change though *)
    (* calls + length l = numCalls?? this is true for the top-level thm (0 + length l = numCalls)*)
    calls + length l = numCalls -> (* this doesn't work, delete? *)
   comp_spec
     (fun (x : list (list (Bvector eta)) * (nat * KV))
        (y : list (list (Bvector eta)) * (nat * KV) * unit) =>
       outputAndKVeq x y)

     (oracleMap (pair_EqDec nat_EqDec eqDecState) (list_EqDec eqdbv)
        (Oi_prg i) (calls, (k1, v)) l)
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (calls, (k2, v)) l) unit unit_EqDec (* note: k's differ. we aren't using this one *)
        (f_oracle f eqdbv k1) tt).
Proof.
  intros.

  destruct l as [ | x xs].
  - 
    simpl in *. omega.
  - clear H_numCalls.
    remember (rev xs) as rev_xs.
    assert (H_revxs: rev (rev xs) = xs).
    { apply rev_involutive. }
    rewrite <- H_revxs.
    rewrite <- Heqrev_xs.
    assert (H_invar : calls + length (x :: rev xs) = numCalls).
    { simpl in *.
      rewrite <- H0.
      f_equal. f_equal. apply rev_length. }
    rewrite <- Heqrev_xs in H_invar.
    clear Heqrev_xs H_revxs H0.
    revert i k1 k2 v calls H_invar.

    induction rev_xs as [ | rev_x' rev_xs']; intros.

    +
      Opaque Oi_prg.
      Opaque Oi_oc'.
      unfold oracleMap.
      simpl.
      fcf_inline_first.
      fcf_skip. admit. admit.   (* what happened to H_invar here? *)
      (* relate Oi_prg and Oi_oc and nil *)
      *
        rename x into numBlocks.
        instantiate (1 := (fun x y => outputAndKVeq x y)).

        (* is this actually false for some values of calls? or not? *)
        (* yeah it's false, take calls > i, then they do GenUpdate and GenUpdate_PRF_OC respectively, but the input keys are different. so here we need to have that calls = 0? like "calls + length l = numCalls"? will that actually make the theorem true? *)
        (* ok this is false but can we add some generalized precondition to make it true? *)
        Transparent Oi_prg. Transparent Oi_oc'.
        unfold Oi_prg. unfold Oi_oc'.
        destruct (lt_dec calls i).
        (* calls < i *)
        { unfold GenUpdate_rb_intermediate. unfold GenUpdate_rb_intermediate_oc.
          simplify. fcf_skip. admit. admit. simplify. fcf_spec_ret. simpl.
          (* oh, actually this isn't even true. do I need that the k's are eq?
           what about the v's? *)
          admit.
        }
        (* calls >= i *)
        { simplify. destruct (beq_nat calls 0).
          (* calls >= i, calls = 0 *)
          { (* why doesn't it simplify? because numBlocks is opaque?
               why did Gen_loop simplify?*)
            unfold GenUpdate_noV.
            unfold GenUpdate_noV_oc.
            simpl.
            fcf_inline_first.
            fcf_skip. admit. admit.
            instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd (snd x) = snd (fst y))).
            admit.

            simpl in H2. destruct H2. destruct b0. destruct b.
            simpl in *. destruct p. simpl in *.
            subst.
            simplify. 
            fcf_spec_ret.
            simpl.
            split. reflexivity.
            f_equal.
            admit.
            (* oh. this is because of v-updating being moved? so k's aren't equal *)
          }
          (* calls >= i, calls != 0 *)
          { 
            destruct (beq_nat calls i).
            (* calls != 0, calls = i *)
            {
              fcf_skip. admit. admit.
              unfold GenUpdate. unfold GenUpdate_oc.
              unfold f_oracle.
              simpl.
              Print outputAndKVeq.
              instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd x = snd (fst y))).
              (* fcf_skip. *) (* why doesn't it work? *)
              fcf_inline_first.
              Print Ltac comp_simp.
              Print Ltac dist_simp_1.
              Print Ltac prog_simp_1.
              prog_ret_r.
              (* is it because Gen_loop is not a <-$... *)
              fcf_ident_expand_l.
              (* this doesn't even return a key *)
              fcf_skip. admit.
              instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd (snd x) = snd (fst y))).
              admit.

              simpl in H2.
              destruct H2.
              destruct b0.
              destruct b.
              simpl in *.
              subst.
              simplify.
              fcf_spec_ret.
              simpl.
              f_equal.
            (* did i mistype something? *)
              admit.

              simpl in H2. destruct b0. destruct H2. simpl in *. destruct p. simpl in *. subst.
              fcf_simp. fcf_spec_ret. simpl. split; reflexivity.
            }
            (* calls > i, calls != 0 *)
            {
              fcf_skip. admit. admit.
              instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd x = snd (fst y))).
              unfold GenUpdate.
              unfold GenUpdate_PRF_oc.
            (* this is just not right because the two keys are different *)
              admit.
              simplify.
              simpl in H2. destruct H2. subst.
              fcf_spec_ret. simpl. split; reflexivity.
            }
          }
        } 
        
        Opaque Oi_prg. Opaque Oi_oc'.

        (* apply Oi_prg_Oi_oc_eq. *)
      * simpl in H2.
        fcf_simp.
        destruct p.
        destruct H2.
        subst.
        simpl.
        fcf_inline_first.
        fcf_simp.               (* well the number of calls should be the same too *)
        fcf_spec_ret.
        simpl.
        split. auto. auto.

    (* inductive case true on reverse *)
    +
      simpl in H_invar.
      (* TODO the problems are that 1. calls isn't changing 2. H_invar disappears *)
      (* how do i get calls to change? calls is linked to the list *)
      (* ideally, when l is revl ++ [a], calls at end of revl is (length revl) going into [a]. will that fix things? *)

      Opaque oracleMap.
      Opaque oracleCompMap_inner.
      simpl.
      Transparent oracleMap.
      Transparent oracleCompMap_inner.
     (* ind hyp holds on (x :: rev rev_xs') so DON'T simpl x out, rewrite w/ fold ++ lemma *)

      rewrite app_comm_cons.
      remember (x :: rev rev_xs') as nonempty.

      unfold oracleMap.
      eapply comp_spec_eq_trans_l.
      apply fold_app_2. admit. admit.

      apply comp_spec_symm.
      eapply comp_spec_eq_trans_l.
      apply oracleCompMap_fold_app. (* is this strong enough? and fold_app_2? *)
      apply comp_spec_symm.

      fcf_skip. admit. admit.
      (* maybe consider not doing a skip here? *)
      (* or, consider proving that state1 = ... and state2 = ... *)
      (* i don't even know how to state this theorem? maybe as a postcondition on each of the first calls here? so the fold_app_2 and oracleCompMap_fold_app (hope this is true?? TODO try) need not change; and there's another postcondition here, and IH should still hold? *)
      (* H_invar disappeared? *)
      {
        (* stronger postcondition here... maybe put in original postcondition actually? *)
        (* time to break everything *)
        (* maybe the new postcondition will get rid of the need for keys being same *)
        apply IHrev_xs'. (* this is wrong now *)
        admit. }
      { simpl in H2.
        simplify.
        destruct p.
        destruct H2.
        subst.
        fcf_skip.
        (* this is different again :| *)
        instantiate (1 := (fun x y => outputAndKVeq x y)). (* not right? *)
        destruct k.
        rename b into k.
        rename b0 into v0.
        Transparent Oi_prg.
        Transparent Oi_oc'.
        unfold Oi_prg.
        unfold Oi_oc'.
        simplify.
        (* fcf_skip. admit. admit. *)
        admit.

        (* we should have: a = n *)
        (* and a = n = len (x :: rev rev_xs') = S (len rev_xs') *)
        (* but EVEN SO, for the base case, `calls` could have been anything (though it's the same between the two, and the base case is still false for some cases of `calls`? *)
        
        (* ok, it just says (l, (a, k, v0)) is whatever the compfold returns (and whatever the oracleCompMap_inner returns); prove/state a lemma about what it returns (e.g. should be S S S calls) -- and how should it relate to the incoming calls and i? see h0 and h1. and see if the lemma actually works, or if we need to prove more stuff  *)

        (* apply Oi_prg_Oi_oc_eq. *)

        (* is there a simpler version of this that i can prove... *)
        (* maybe i can prove they're equal for all calls (destruct)?? then i don't need to retain that information *)
        (* no but i need the information so i can reason about the different key inputs in this case... *)
        (* how would i do this on paper? *)

        (* they're the same BUT NOT LINKED WITH k1. woops. wrong postcondition again?? *)
        (* or can this be proved depending on what i is? *)
        (* ok maybe it's my problem? maybe k1 should be updated for f. does the key for f ever change? should it? it should change to be the same key as Oi_oc''s? but it's never output? so how can we write a postcondition about this? oh no f's key is never updated but it should be?? thanks coq *)
        (* ok i have no idea 1. how many other proofs this breaks 2. how to fix it (how do i even update an oracle?) *)
        (* in fact the behavior is completely different if you consider the case of 
PRF PRF..PRF -- k is never updated in the latter *)
        (* ok if you change the GenUpdates to use f k instead f_oracle after the first call... it should fix things... is it the best fix? idk *)
        (* wait no, it already does that (GenUpdate_PRF_oc). so not everything is on fire? *)
        (* but i lost information about which call (callsSoFar) it is. does this need to be encoded in the inductive invariant? *)
        (* still idk if the postcondition is right? *)

        simpl in H4.
        simplify.
        destruct p.
        destruct H4.
        subst.
        fcf_spec_ret.
        simpl.
        split. auto. auto. }
Qed.

Transparent oracleMap.
Transparent oracleCompMap_inner.
Transparent Oi_prg.
Transparent Oi_oc'.

(* TODO have not applied above lemma to the below lemma yet *)

(* this moves from the normal adversary to the PRF adversary (which depends on the prev.) *)
(* Gi_prg 0: PRF PRF PRF PRF
   Gi_prf 0: PRF PRF PRF PRF
   Gi_prg 2: RB RB PRF PRF
   Gi_prf 2: RB RB PRF PRF *)
(* TODO: start proving this lemma first? how do i prove it?
need to reason that passing in PRF oracle to GenUpdate_oc is equivalent to just using GenUpdate (there's also a GenUpdate_PRF_oc) *)
Lemma Gi_normal_prf_eq : forall (i : nat),
  Pr[Gi_prg i] == Pr[Gi_prf i].
Proof.
  intros.
  unfold Gi_prg.
  unfold Gi_prf.
  unfold PRF_Adversary.

  fcf_to_prhl_eq.
  unfold Instantiate.
  (* TODO: can't figure out how to resolve "l > 0" problem above, commented it out and now am trying to figure out if the keys HAVE to be different *)
  (* first k is generated on the right for f; on the left, generates (k,v) for oracle use (which is actually used if it's all PRF or overridden if it starts with at least one RB)... so, should I have skipped here?
    i feel like what we have is right. the keys are the same b/t f and oracleMap
and i can't swap lines because the second depends on it
    wait, so what was the technical reason it wouldn't unify in the previous lemma? if no hyp about list len, then if the 2 keys are different, it's false in the 'list = nil' case.
*)
  unfold oracleCompMap_outer.
  fcf_inline_first.

  unfold Instantiate.
  comp_skip.                    (* TODO should I do this? *)
  Opaque oracleMap.
  simpl.
  fcf_inline_first.

  (* remember x as k. *)
  (* fcf_irr_l. unfold RndV. fcf_well_formed.  *)
  unfold Instantiate.
  fcf_inline_first.
  fcf_irr_r. unfold RndK. fcf_well_formed.
  fcf_inline_first.
  comp_skip.
  fcf_simp.
  simpl.
  fcf_inline_first.
  fcf_skip.

  instantiate (1 := fun x y => outputAndKVeq x y).
  -
    Transparent oracleMap.
    apply Gi_normal_prf_eq_compspec.
    unfold maxCallsAndBlocks.
    rewrite length_replicate.
    omega.

  - fcf_simp.
    simpl in *.
    destruct p.
    destruct H6.
    subst.
    fcf_inline_first.
    fcf_simp.
    fcf_inline_first.
    fcf_ident_expand_l.         (* lol *)
    fcf_skip.
    fcf_simp.
    fcf_reflexivity.
Qed.

(* expose the bad event (dups) *)
Lemma Gi_rf_return_bad_eq : forall (i : nat),
    Pr[Gi_rf i] == Pr[x <-$ Gi_rf_bad i; ret fst x].
Proof.
Admitted.

Definition randomFunc_withDups ls x :=
  y <-$ 
    (match (arrayLookup _ ls x) with 
     | Some y => ret y 
     | None => {0,1}^eta 
     end); 
  ret (y, (x, y) :: ls).

(* ith game: use RF oracle *)
Definition Gi_rf_dups_bad (i : nat) : Comp (bool * bool) :=
  [b, state] <-$2 PRF_Adversary i _ _ randomFunc_withDups nil;
  ret (b, hasInputDups state). 

Lemma Gi_rf_dups_return_bad_eq : forall (i : nat),
    Pr[x <-$ Gi_rf_bad i; ret fst x] == Pr[x <-$ Gi_rf_dups_bad i; ret fst x].
Proof.
Admitted.

(* expose the bad event (dups) *)
Lemma Gi_rb_return_bad_eq : forall (i : nat),
    Pr[Gi_rb i] == Pr[x <-$ Gi_rb_bad i; ret fst x].
Proof.
Admitted.

(* does not hold for i = 0:
Gi_prg 0: PRF PRF PRF...
Gi_prg 1: RB PRF PRF...
Gi_rb 0 : RB PRF PRF... 
(call number 0 uses the RB oracle) -- equivalence, no replacing happening here *)
(* might have misnumbered something here? *)
(* using random bits as the oracle for the ith call = the (i+1)th hybrid *)
Transparent Oi_prg.
Lemma Gi_normal_rb_eq : forall (i : nat),
    Pr[Gi_prg (S i)] == Pr[Gi_rb i].
Proof.
  intros.
  unfold Gi_prg.
  unfold Gi_rb.
  unfold Oi_prg.

  unfold PRF_Adversary.
  unfold Oi_oc'.

(* relate Oi_prg with Oi_oc'? (they need better names?) *)
  unfold oracleCompMap_outer.
  (* do i have to induct? induction hypothesis doesn't help *)
(* e.g. note that the instantiate has moved inside the oracleCompMap *)
  (* also have to show that that passed-in RB oracle is equivalent to GenUpdate_rb_intermediate *)
  (* want to destruct on: callsSoFar < i, = i, > i *)
  (* but other one is lt_dec callsSoFar (S i) *)
  
  simpl.                        (* ? *)
  fcf_inline_first.
  fcf_skip.
  fcf_skip.
  fcf_simp.
  simpl.
  fcf_inline_first.             (* ?? *)
  (* what relation applies on these two? and can i even skip? *)
  (* fcf_skip. *)

Admitted.

(* ----------------------- *Identical until bad section *)

(* SAME PROOF AS PRF_A_randomFunc_eq_until_bad (with the computation order switched) *)
Theorem oracleCompMap__oracle_eq_until_bad_dups : forall (i : nat) b b0,
    comp_spec
     (fun y1 y2 : list (list (Bvector eta)) * list (Blist * Bvector eta) =>
        (* TODO fix args *)
        (* let (bits_rb, state_rb) := y1 in *)
        (* let (bits_rf, state_rf) := y2 in *)
        (* let (inputs_rb, outputs_rb) := (fst (split state_rb), snd (split state_rb)) in *)
        (* let (inputs_rf, output_rf) := (fst (split state_rf), snd (split state_rf)) in *)
        hasDups _ (fst (split (snd y1))) = hasDups _ (fst (split (snd y2))) /\
        (hasDups _ (fst (split (snd y1))) = false ->
         snd y1 = snd y2 /\ fst y1 = fst y2))

     ((z <--$
       oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (O, (b, b0)) maxCallsAndBlocks; [bits, _]<-2 z; $ ret bits)
        (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
        rb_oracle nil)
     ((z <--$
       oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (O, (b, b0)) maxCallsAndBlocks; [bits, _]<-2 z; $ ret bits)
        (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
        randomFunc_withDups nil).
Proof.
  intros.
  (* TODO review this *)
  eapply (fcf_oracle_eq_until_bad
            (fun x => hasDups _ (fst (split x)))
            (fun x => hasDups _ (fst (split x))) eq); intuition.

  - fcf_well_formed. admit.
  - intros. unfold rb_oracle. fcf_well_formed.
  - intros. unfold randomFunc_withDups. destruct (arrayLookup eqdbl a b1); fcf_well_formed.
  - 
    subst.
    unfold randomFunc_withDups, rb_oracle.

    (* x2 is the list, a is the element. change variable names *)
    case_eq (arrayLookup _ x2 a); intuition.

      (* is a duplicate (a is in x2) *)
      (* now we need to prove that, given that a is in x2,
         the postcondition holds: 
         note that they both have state x2
       *)
    * fcf_irr_l.
      fcf_simp.
      (* note the simplified state here *)
      (*  (ret (b, (a, b) :: x2))
          (ret (b0, (a, b0) :: x2)) 
         - we know a is in x2 for both
         - b0 is some random bitvector, b is whatever the lookup returns for a *)
      fcf_spec_ret; simpl.

      (* note the 3 new goals *)
      (* obviously hasDups (thing1 :: x2) = hasDups (thing2 :: x2), since `hasDups x2` *)
      + remember (split x2) as z.
        destruct z.
        Print hasDups.
        (* Print in_dec. *) (* looks gnarly *)
        (* hasDups added and removed here! :^) *)
        simpl in *.
        trivial.

      (* snd y1 = snd y2 (if there are no dups in the whole state, then the states are the same. but we know there are dups in x2, the tail of the state, so, contradiction!) *)
      + simpl in *.
        remember (split x2) as z.
        destruct z.
        simpl in *.
        destruct (in_dec (EqDec_dec eqdbl) a l); intuition.
        discriminate.
        rewrite notInArrayLookupNone in H.
        discriminate.
        intuition.
        rewrite unzip_eq_split in H4.
        remember (split x2) as z.
        destruct z.
        pairInv.
        simpl in *.
        intuition.

      (* fst y1 = fst y2 (exactly the same as above! if there are no dups in the whole state... but we know there are dups in the tail of the state, so, contradiction!) *)
      + simpl in *.
        remember (split x2) as z.
        destruct z.
        simpl in *.
        destruct (in_dec (EqDec_dec eqdbl) a l).
        discriminate.
        rewrite notInArrayLookupNone in H.
        discriminate.
        intuition.
        rewrite unzip_eq_split in H4.
        remember (split x2) as z.
        destruct z.
        pairInv.
        simpl in *.
        intuition.

    * (* not a duplicate -- behaves like RB -- a is not in x2 *)
      fcf_skip.
      fcf_spec_ret.

    - unfold rb_oracle in *.
      fcf_simp_in_support.      (* 6 *)
      simpl in *.
      remember (split c0) as z.
      destruct z.
      simpl in *.
      destruct (in_dec (EqDec_dec eqdbl) d l).
      intuition.
      intuition.

    - (* want to prove: for both oracles, if the state starts bad, it stays bad *)
      (* dups in c0 inputs, and when randomFunc_withDups is run with that state it returns output a and state b, there are dups in the inputs of that state *)
      unfold randomFunc_withDups in *. (* 5 *)
      (* NOTE this is a useful tactic *)
      fcf_simp_in_support.
      simpl.
      remember (split c0) as z.
      destruct z.
      simpl in *.
      destruct (in_dec (EqDec_dec eqdbl) d l).
      intuition.             (* first element is dup *)
      intuition. (* by H -- the existing state has dups *)
Qed.

Theorem PRF_Adv_eq_until_bad : forall (i : nat),
   comp_spec 
     (fun a b : bool * list (Blist * Bvector eta) =>
        let (adv_rb, state_rb) := a in
        let (adv_rf, state_rf) := b in
        let (inputs_rb, outputs_rb) := (fst (split state_rb), snd (split state_rb)) in
        let (inputs_rf, output_rf) := (fst (split state_rf), snd (split state_rf)) in
        hasDups _ inputs_rb = hasDups _ inputs_rf /\
        (hasDups _ inputs_rb = false ->
         (* true -- if there are no duplicates, then the random function behaves exactly like RB, so the key is randomly sampled AND the v (going into the PRF) is also randomly sampled. so the outputs should be the same.
in fact, if there are no dups, PRF_Adv rf i = PRF_Adv rb i.
so, this means the comp_spec above is true?
does PRHL act like giving each the same "tape" of randomness for equality? *)
         state_rb = state_rf /\ adv_rb = adv_rf))
     ((PRF_Adversary i) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle nil)
     ((PRF_Adversary i) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv))
        randomFunc_withDups nil).
Proof.
  intros.
  unfold PRF_Adversary.
  simpl.
  fcf_inline_first.
  fcf_skip.
  fcf_simp.
  fcf_skip.
  apply oracleCompMap__oracle_eq_until_bad_dups.

  (* ------ *)
  fcf_simp.
  intuition.
  rename b1 into state_rb_.
  rename l0 into state_rf_.
  rename a0 into bits_rb_.
  rename l into bits_rf_.

  (* case_eq shows up in both *)
  Print Ltac case_eq.
  Locate Ltac case_eq.
  (* TODO what is this? *)

  (* case_eq (hasInputDups state_rb_); intuition. *)
  case_eq (hasDups _ (fst (split (state_rb_)))); intuition.

  (* duplicates exist, computations are irrelevant *)
  - 
    fcf_irr_l.
    fcf_irr_r.
    rename a into adv_rb_.
    rename b1 into adv_rf_.
    fcf_spec_ret.
    (* true=false in hypotheses *)
    (* hasInputDups state_rb_ = true (by case_eq) and false (by assumption in postcondition) *)
    congruence.

  (* no duplicates, equality is preserved *)
  (* automatically applied dups = false to get that the states and outputs are the same *)
  - simpl in *.
    subst.
    fcf_skip.
    fcf_spec_ret.
Qed.

(* ------------------------------ *)
(* Update: use Adam's code above but with hasDups *)

(* Takes a while to evaluate, so commented out.

(* replace blocksPerCall with an n we can evaluate on *)
Definition Game_GenUpdate_oc_call_n
           (oracle  : list (Blist * Bvector eta) -> Blist
                      -> Comp (Bvector eta * list (Blist * Bvector eta)))
           (n : nat)
           : Comp (bool * bool) :=
  state <-$ Instantiate;
  [res, state] <-$2 GenUpdate_oc state n _ _ oracle nil;
  (* should the initial oracle state be nil? *)
  [bits, kv] <-2 res;
  res <-$ A (bits :: nil);
  ret (res, hasDups _ state).            (* don't need the ending KV state *)

Open Scope nat.
Lemma Gi_rf_bad_eq_snd_test1 : 
    Pr [x <-$ Gi_rb_bad_l 0 (1::nil); ret snd x ] ==
    Pr [x <-$ Game_GenUpdate_oc_call_n rb_oracle 1; ret snd x ].
Proof.
  intros.
  unfold Gi_rb_bad_l.
  unfold PRF_Adversary_l.
  unfold Game_GenUpdate_oc_call_n.
  unfold Oi_oc'.
  (* this might be using the wrong oracle? *)
  Opaque GenUpdate_noV_oc.
    simpl.
    (* it's using GenUpdate_noV_oc -- where it should be using GenUpdate_oc? i thought i'd fixed this. does this work for n > 1 (and for certain i) though? *)
    (* if there's only 1 call, we should definitely be using the oracle on that call, so we can correctly prove the one-call case (PRF -> RF -> RB) *)
    Transparent GenUpdate_noV_oc.
    unfold GenUpdate_noV_oc.
    unfold Gen_loop_oc.
    (* oh -- doesn't update v. but is Pr Collisions still the same? *)
    (* (output are the same, state is different) *)

  unfold GenUpdate_oc.  (* updates v, Generates one block (updates v once -- be more accurate), updates k *)
  unfold Gen_loop_oc.
  simplify.
  fcf_skip.
  simplify.
  fcf_skip.
  Opaque hasDups.
  simpl.
  fcf_inline_first.
  fcf_simp.
  fcf_irr_l. admit.
  Opaque evalDist_OC.
  fcf_inline_first.
  simpl.
  fcf_to_prhl.
  Transparent evalDist_OC.
  simplify.

  (* new *)
  unfold rb_oracle.
  simplify.
  fcf_skip.
  simplify.
  fcf_irr_r.
  simplify.
  fcf_irr_r.
  simplify.
  fcf_skip_eq. admit.
  simplify.
  fcf_to_probability. admit. admit.
(* all vars are from the same distribution? but some aren't independent? *)
  
  (* isn't this equivalent to a0 = b2? *)
(* there's an extra element in the latter list -- extra update *)
(* also some of the elements are the same between them (b, x0) and some are different *)
(* TODO *)
Admitted.

Lemma Gi_rf_bad_eq_snd_test2 : 
    Pr [x <-$ Gi_rb_bad_l 1 (1::nil); ret snd x ] ==
    Pr [x <-$ Game_GenUpdate_oc_call_n rb_oracle 1; ret snd x ].
Proof.
  intros.
  unfold Gi_rb_bad_l.
  unfold PRF_Adversary_l.
  unfold Game_GenUpdate_oc_call_n.
  simplify.
  fcf_skip.
  simplify.
  fcf_skip.
  simplify.
  fcf_skip.
  simplify.
  fcf_irr_r. admit.             (* ? *)
  simplify.
  fcf_irr_r. admit.
  Opaque hasDups.
  simplify.
  fcf_to_prhl.
  fcf_skip_eq. simpl in *. admit. (* ? *)
  fcf_simp.
  simpl.

  (* the oracle state of the former (in Gi_rb_bad_l) is nil because the oracle didn't get called since i = 1. so, that confirms my hypothesis that i should just be using hasDups? *)
Admitted.

(* OVER length of first list, items in first list / ith items, and ? *)
(* does not evaluate quickly, so commented out *)
(* Lemma Gi_rf_bad_eq_snd_test3 : 
    Pr [x <-$ Gi_rb_bad_l 1 (1::1::nil); ret snd x ] ==
    Pr [x <-$ Game_GenUpdate_oc_call_n rb_oracle 1; ret snd x ].
Proof.
  intros.
  unfold Gi_rb_bad_l.
  unfold PRF_Adversary_l.
  unfold Game_GenUpdate_oc_call_n.
  simplify.
  fcf_skip.
  simplify.
  fcf_skip.
  simplify.
  fcf_skip.

  fcf_simp.
  Opaque Oi_oc'.
  Opaque evalDist_OC.
  fcf_inline_first.
  fcf_irr_r. admit.
  fcf_simp.
  fcf_inline_first.
  fcf_simp.

  Transparent Oi_oc'.
  fcf_to_prhl.

Admitted. *) *)

(* First assumption for id until bad: the two games have the same probability of returning bad *)
(* uses provided oracle on call number i
   i = 2
                      0  1  2   3   4
   Gi_rf_bad i =     RB RB RF PRF  PRF
   Gi_rb_bad i =     RB RB RB PRF PRF
   bad event = duplicates in input on call number i *)
Lemma Gi_rb_rf_return_bad_same : forall (i : nat),
    Pr  [x <-$ Gi_rb_bad i; ret snd x ] ==
    Pr  [x <-$ Gi_rf_dups_bad i; ret snd x ].
Proof.
  intros.
  unfold Gi_rb_bad. unfold Gi_rf_dups_bad.
  fcf_to_prhl_eq.
  fcf_inline_first.
  fcf_skip.
  (* different spec if you do `fcf_to_prhl` only, and in this location *)
  *
    Check PRF_Adv_eq_until_bad.
    apply PRF_Adv_eq_until_bad.
  *
    destruct b0.
    intuition.
    fcf_simp.
    unfold hasInputDups.
    rewrite H2.
    simpl.
    fcf_reflexivity.
Qed.

(* "distribution of the value of interest is the same in c_1 and c_2 when the bad event does not happen" -- the two are basically the same if the bad event doesn't happen, so it's true.
         differences: 1. PRF re-keyed using RF vs. randomly sampled. but PRF re-keyed using something of length > eta, so it is effectively randomly sampled.
         2. the v going into the next call (if it exists) is randomly sampled vs. resulting from a RF call, but it doesn't matter *)

(* TODO: both of these proofs (in PRF_DRBG) rely on the PRF_Adv comp_spec lemma, which is proven by a bunch of casework. need another comp_spec lemma here on genupdate/prfadv? that adversary isn't even here anymore... *)

Theorem Gi_rb_rf_no_bad_same : forall (i : nat) (a : bool),
   evalDist (Gi_rb_bad i) (a, false) == evalDist (Gi_rf_dups_bad i) (a, false).
Proof.
  intros.
  fcf_to_prhl.                  (* note the auto-specification here *)
  (* it's NOT fcf_to_prhl_eq *)
  unfold Gi_rb_bad.
  unfold Gi_rf_dups_bad.
  fcf_skip.
  *
    apply PRF_Adv_eq_until_bad.
    (* but is this the right specification? *)
  *
    fcf_simp.
    intuition.
    fcf_spec_ret.

    pairInv.
    unfold hasInputDups.
    apply H3 in H6.
    intuition.
    subst.
    reflexivity.

    pairInv.
    unfold hasInputDups in *.
    rewrite H2.
    rewrite <- H2 in H6.
    apply H3 in H6.
    intuition.
    subst.
    fcf_reflexivity.
Qed.

(* Applying the fundamental lemma here *)
Lemma Gi_rb_rf_identical_until_bad : forall (i : nat),
| Pr[x <-$ Gi_rf_dups_bad i; ret fst x] - Pr[x <-$ Gi_rb_bad i; ret fst x] | <=
                                              Pr[x <-$ Gi_rb_bad i; ret snd x].
Proof.
  intros. rewrite ratDistance_comm.

  fcf_fundamental_lemma.

  (* TODO: confirm if these assumptions seem true *)
  (* first assumption: they have same probability of returning bad *)
  - apply Gi_rb_rf_return_bad_same.

  (* "distribution of the value of interest is the same in c_1 and c_2 when the bad event does not happen" *)
  - apply Gi_rb_rf_no_bad_same.
Qed.

(* ----------- End identical until bad section *)

(* adam wrote a new game here -- bad event is repetition in the random INPUTS
INPUTS = v :: (first n of outputs)? *)
(* modified PRF_Adversary to just return bits *)
Definition callMapWith (i : nat) : OracleComp Blist (Bvector eta) (list (list (Bvector eta))) :=
  bits <--$ oracleCompMap_outer _ _ (Oi_oc' i) maxCallsAndBlocks;
  $ ret bits.

(* throw away the first input and the adversary, focus on bad event only *)
Definition Gi_rb_bad_no_adv (i : nat) : Comp bool :=
  [_, state] <-$2 callMapWith i _ _ rb_oracle nil;
  ret (hasInputDups state).

(* throw away all other inputs/outputs but the ones in the "ith" call ((k,v) are randomly sampled going into the hybrid ith call anyway) *)
(* the oracle's state is unaffected by computations around it  *)
Definition Gi_rb_bad_only_oracle : Comp bool :=
  [k, v] <-$2 Instantiate;
  [_, state] <-$2 GenUpdate_oc (k, v) blocksPerCall _ _ rb_oracle nil;
  (* this used to be dupsInIthInputCall O, so check that the lemmas about this are right *)
  ret (hasInputDups state).

(* next, inline the RB oracle (change oracle computation to normal computation) and get the inputs in terms of the outputs etc. modify the type so that it returns the two internal inputs to the oracle as well (which we need for the game) *)
(* using Gen_loop_rb; need to slightly modify GenUpdate_rb_intermediate to get the calls 
similar to Adam's PRF_DRBG_f_bad_2 *)
Definition GenUpdate_rb_inputs (state : KV) (n : nat)
  : Comp (list (Bvector eta) * KV * (Bvector eta * Blist)) :=
  [k, v] <-2 state;
  v' <-$ {0,1}^eta;
  [bits, v''] <-$2 Gen_loop_rb_intermediate k v' n; (* could probably simplify GLRI *)
  k' <-$ {0,1}^eta;                                 (* could probably remove this *)
  ret (bits, (k', v''), (v', (to_list v'' ++ zeroes))).

Definition Gi_rb_bad_no_oracle : Comp bool :=
  [k, v] <-$2 Instantiate;
  [bits, kv_state, otherInputs] <-$3 GenUpdate_rb_inputs (k, v) blocksPerCall;
  [v', keyInput] <-2 otherInputs;
  (* annoying, everything is converted to lists, so now i need to reason that all the lists have the same length except the key-refreshing input list *)
  let firstInput := to_list v in (* fixed *)
  let nextInput := to_list v' in (* extra input to refresh the v *)
  let outputsAsInputs := firstn (blocksPerCall - 1) (map (fun v => to_list v) bits) in (* only the outputs (so v' is not duplicated) -- we need to remove the last output because that isn't used as an input. OR we can leave it in and get a slightly worse bound. *)
  ret (hasDups _ (keyInput :: firstInput :: nextInput :: outputsAsInputs)).

(* remove the v input, cons the fixed v to the beginning, and map all the bvector outputs to blist. corresponds to Adam's PRF_DRBG_f_bad_2 and PRF_DRBG_G3_bad_2. uses Gen_loop_rb.
can't use GenUpdate_rb because i need the v and k update inputs *)

(* --- *)
(* without k, still using first v (because we need a v) -- modified to return last v
is there an easier way? maybe using firstn (blocksPerCall - 1) and skipn *)
Fixpoint Gen_loop_rb_no_k (v : Bvector eta) (n : nat) :
  Comp (list (Bvector eta) * Bvector eta) :=
  match n with
  | O => ret (nil, v)
  | S n' =>
    v' <-$ {0,1}^eta;
    [bits, v''] <-$2 Gen_loop_rb_no_k v' n';
    ret (v' :: bits, v'')
  end.

(* the first v is still an input to the oracle, but this GenUpdate doesn't need it
also, we don't care about k: never used as an input, and its output doesn't matter 
also, v'' itself is not used as an input *)
Definition GenUpdate_rb_no_k (n : nat)
  : Comp (Bvector eta * list (Bvector eta) * Blist) :=
  v' <-$ {0,1}^eta;
  [bits, v''] <-$2 Gen_loop_rb_no_k v' blocksPerCall;
  ret (v', bits, (to_list v'' ++ zeroes)).

Definition Gi_rb_bad_no_k : Comp bool :=
  v <-$ RndV;
  [v', bits, keyInput] <-$3 GenUpdate_rb_no_k blocksPerCall;
  let firstInput := to_list v in (* fixed *)
  let nextInput := to_list v' in (* extra input to the loop -- the refreshed v *)
  let outputsAsInputs := firstn (blocksPerCall - 1) (map (fun v => to_list v) bits) in 
  ret (hasDups _ (keyInput :: firstInput :: nextInput :: outputsAsInputs)).

(* ---- *)
(* *have* to apply the injection to_list : forall eta, Bvector eta -> Blist, since there's one input of a different length, so skip that game *)
(*    Definition PRF_DRBG_G3_bad_3 :=
     ls <-$ compMap _ (fun _ => {0, 1}^eta) (forNats (pred l));
     ret (hasDups _ (v_init :: (map injD ls))). *)

(* get it to look like compMap and remove the GenUpdate *)
(* this is basically compMap but carrying around an extra element... prove equivalence *)
(* Fixpoint Gen_loop_rb_map (v : Bvector eta) (n : nat) : *)
(*   Comp (list (Bvector eta) * Bvector eta) := *)
(*   match n with *)
(*   | O => ret (nil, v) *)
(*   | S n' => *)
(*     v' <-$ {0,1}^eta; *)
(*     [bits, v''] <-$2 Gen_loop_rb_no_k v' n'; *)
(*     ret (v' :: bits, v'') *)
(*   end. *)

(* Definition lastElem {A : Type} (l : list A) (default : A) : A := *)
(*   match l with *)
(*   | nil => default *)
(*   | x :: *)

(* inline GenUpdate and Gen_loop, change Gen_loop to a map
remove v'' from the end (it's never used as an input) and generate it separately
(only (to_list v'' ++ zeroes) is used as an input *)

(*    Definition PRF_DRBG_G3_bad_3 :=
     ls <-$ compMap _ (fun _ => {0, 1}^eta) (forNats (pred l));
     ret (hasDups _ (v_init :: (map injD ls))).

^ why is there a (-1) here? *)

Definition Gi_rb_bad_map : Comp bool :=
  v <-$ RndV;
  v' <-$ {0,1}^eta;
  bits <-$ compMap _ (fun _ => {0,1}^eta) (forNats (blocksPerCall - 1)); (* ? *)
  v'' <-$ {0,1}^eta;            (* TODO check if this is ok -- should it be -2 above? *)
  (* not quite right -- blocksPerCall could be 1 -- TODO fix "last elem" everywhere *)
  let firstInput := to_list v in (* fixed *)
  let nextInput := to_list v' in (* extra input to refresh the v *)
  let keyInput := to_list v'' ++ zeroes in
  let outputsAsInputs := map (fun v => to_list v) bits in
  (* took the last block off, so don't need firstn anymore *)
  (* keyInput isn't a dup; firstInput is fixed, and inline nextInput into compMap *)
  ret (hasDups _ (keyInput :: firstInput :: nextInput :: outputsAsInputs)).

(* absorb v' into compMap *)
Definition Gi_rb_bad_map_inline : Comp bool :=
  v <-$ RndV;
  bits <-$ compMap _ (fun _ => {0,1}^eta) (forNats blocksPerCall); 
  v'' <-$ {0,1}^eta;            (* TODO check if this is ok -- should it be -2 above? *)
  (* not quite right -- blocksPerCall could be 1 -- TODO fix "last elem" everywhere? *)
  let firstInput := to_list v in (* fixed *)
  let keyInput := to_list v'' ++ zeroes in
  let outputsAsInputs := map (fun v => to_list v) bits in
  (* keyInput isn't a dup; firstInput is fixed, and inline nextInput into compMap *)
  ret (hasDups _ (keyInput :: firstInput :: outputsAsInputs)).

(* keyInput cannot collide with any other input, so remove it and the listifying *)
Definition Gi_rb_bad_map_no_keyinput : Comp bool :=
  v <-$ RndV;                   (* is {0,1}^eta, but should I leave it fixed?? TODO*)
  bits <-$ compMap _ (fun _ => {0,1}^eta) (forNats blocksPerCall); 
  ret (hasDups _ (v :: bits)).

(* v is randomly sampled here... but sometimes it's fixed (as in PRF_DRBG)? TODO *)
(* seems too simple *)
Definition Gi_rb_bad_map_inline_v : Comp bool :=
  bits <-$ compMap (Bvector_EqDec eta) (fun _ => {0,1}^eta) (forNats (S blocksPerCall)); 
  ret (hasDups (Bvector_EqDec eta) bits).

(* some of these inlinings can probably be done better in a different order or simultaneously *)

(* todo: get it to a point where I can apply Adam's lemma with a different size *)
(* specifically figure out how much of it i can reuse.
- can i only use the very last one? 

   Theorem dupProb_const : 
    forall (X : Set)(ls : list X)(v : Bvector eta),
      (* why not put PRF_DRBG_G3_bad_4 here? *)
      Pr[x <-$ compMap _ (fun _ => {0, 1}^eta) ls; ret (hasDups _ (v :: x))] <= 
      ((S (length ls)) ^ 2 / 2 ^ eta).

- at what point can i plug into the intermediate games?
- the PRF_DRBG oracle constructions are slightly different
- can i even instantiate his module's types? *)

(* TODO: write that these games have the same probability, then rewrite below *)
(* should be easy *)
Lemma Gi_rb_bad_eq_1 : forall (i : nat),
    Pr [x <-$ Gi_rb_bad i; ret snd x] = Pr [Gi_rb_bad_no_adv i].
Proof.
  intros.
  unfold Gi_rb_bad.
  unfold Gi_rb_bad_no_adv.
Admitted.  

Lemma Gi_rb_bad_eq_2 : forall (i : nat),
    Pr [Gi_rb_bad_no_adv i] = Pr [Gi_rb_bad_only_oracle].
Proof.
  intros.
  unfold Gi_rb_bad_no_adv.
  unfold Gi_rb_bad_only_oracle.
  unfold callMapWith.
  unfold oracleCompMap_outer.
  unfold oracleCompMap_inner.
  unfold Oi_oc'.

(* left hand side: RB' RB RB RF PRF PRF...
   right hand side:          RF            *)
  
Admitted.

(* note: no nat *)
Lemma Gi_rb_bad_eq_3 : 
    Pr [Gi_rb_bad_only_oracle] = Pr [Gi_rb_bad_no_oracle].
Proof.
  intros.
Admitted.

(* no k *)
Lemma Gi_rb_bad_eq_4 : 
    Pr [Gi_rb_bad_no_oracle] = Pr [Gi_rb_bad_no_k].
Proof.
  intros.
Admitted.

Lemma Gi_rb_bad_eq_5 : 
    Pr [Gi_rb_bad_no_k] = Pr [Gi_rb_bad_map].
Proof.
  intros.
Admitted.

Lemma Gi_rb_bad_eq_6 : 
    Pr [Gi_rb_bad_map] = Pr [Gi_rb_bad_map_inline].
Proof.
  intros.
Admitted.

Lemma Gi_rb_bad_eq_7 : 
    Pr [Gi_rb_bad_map_inline] = Pr [Gi_rb_bad_map_no_keyinput].
Proof.
  intros.
Admitted.

Lemma Gi_rb_bad_eq_8 : 
    Pr [Gi_rb_bad_map_no_keyinput] = Pr [Gi_rb_bad_map_inline_v].
Proof.
  intros.
Admitted.

(* probability of bad event happening in RB game is bounded by the probability of collisions in a list of length (n+1) of randomly-sampled (Bvector eta) *)
Lemma Gi_rb_bad_collisions : forall (i : nat),
   Pr  [x <-$ Gi_rb_bad i; ret snd x ] <= Pr_collisions.
Proof.
  intros.
  rewrite Gi_rb_bad_eq_1.
  rewrite Gi_rb_bad_eq_2.
  rewrite Gi_rb_bad_eq_3.
  rewrite Gi_rb_bad_eq_4.
  rewrite Gi_rb_bad_eq_5.       (* questionable *)
  rewrite Gi_rb_bad_eq_6.
  rewrite Gi_rb_bad_eq_7.
  rewrite Gi_rb_bad_eq_8.
  unfold Gi_rb_bad_map_inline_v.
  
  Opaque hasDups.
  unfold Pr_collisions.
  Check dupProb.
  generalize dupProb.
  intros dupProb.

(* TODO there's a more general lemma *)
  assert (length (forNats (S blocksPerCall)) = S blocksPerCall).
  { admit. }
  rewrite <- H at 2.
  (* apply Adam's collision bound here *)
  apply dupProb.

  (* didn't need either of these (work from PRF_DRBG) TODO *)
  (* apply FixedInRndList_prob. *)
  (* apply dupProb_const. *)
Qed.

(* Main theorem (modeled on PRF_DRBG_G3_G4_close) *)
(* Gi_rf 0:  RF  PRF PRF
Gi_prg 1:    RB PRF PRF

Gi_rf  1:    RB  RF PRF
Gi_prg 2:    RB  RB  PRF

Gi_rf  2:    RB  RB  RF
Gi_prg 3:    RB  RB  RB *)
Lemma Gi_rf_rb_close : forall (i : nat), (* not true for i = 0 (and not needed) *)
  | Pr[Gi_rf i] - Pr[Gi_prg (S i)] | <= Pr_collisions.
Proof.
  intros.
  rewrite Gi_normal_rb_eq. (* put Gi_prg into the same form using RB oracle *)
  (* TODO this might be wrong, maybe Gi_prg (S i) = Gi_rb (S i) *)
  (* shouldn't we be relating
     RB RB RF PRF with  <- Gi_rf 2
     RB RB RB PRF ? <-- Gi_prg 3 = Gi_rb 2
 *)

  rewrite Gi_rf_return_bad_eq. 
  rewrite Gi_rb_return_bad_eq. 
  rewrite Gi_rf_dups_return_bad_eq.

  rewrite Gi_rb_rf_identical_until_bad.
  apply Gi_rb_bad_collisions.

(* want lemmas saying
- key updating: calling a RF with an input of longer length whereas all other inputs had same length = randomly sampled <<<

- previous RB output (if any) are indistinguishable <<<
- succeeding PRF output (if any) are indistinguishable
  - uses key updating lemma above
  - v-updating: 
- only the RB/RF outputs may be distinguishable
  - the K, V inputs are randomly sampled
  - distinguishable with advantage Pr_collisions = (blocksPerCall + 1)^2 / 2^eta
  - because of key updating lemma above (adv 0)
  - plus adam's lemma with an additional list entry

- other wrinkles: dealing with OracleComp stuff, PRF_Adversary *)
Qed.

(* Inductive step *)
(* let i = 3. 
Gi_prg i:      RB RB RB PRF PRF
Gi_prg (S i):  RB RB RB RB  PRF 

Gi_prg 0: PRF PRF PRF
Gi_rf  0:  RF PRF PRF
Gi_prg 1:  RB PRF PRF
Gi_rf  1:  RB  RF PRF *)
Theorem Gi_Gi_plus_1_close :
  (* TODO: constructed PRF adversary *)
  forall (n : nat),
  | Pr[Gi_prg n] - Pr[Gi_prg (S n)] | <= Gi_Gi_plus_1_bound.
Proof.
  unfold Gi_Gi_plus_1_bound. intros.
  eapply ratDistance_le_trans. (* do the PRF advantage and collision bound separately *)
  rewrite Gi_normal_prf_eq.    (* changed this *)
  Print Gi_prf.
  apply Gi_prf_rf_close.        (* Basically already proven via PRF_Advantage magic *)
  apply Gi_rf_rb_close.
Qed.

(* ------------------------------- *)

(* final theorem *)
Theorem G1_G2_close :
  (* TODO: constructed PRF adversary *)
  (* | Pr[G1_prg] - Pr[G2_prg] | <= (q / 1) * (PRF_Advantage RndK ({0,1}^eta) f _ _ ). *)
  | Pr[G1_prg] - Pr[G2_prg] | <= (numCalls / 1) * Gi_Gi_plus_1_bound.
Proof.
  rewrite G1_Gi_O_equal.
  rewrite G2_Gi_n_equal.
  (* rewrite ratDistance_comm. *)
  Check distance_le_prod_f.
  (* inductive argument *)
  specialize (distance_le_prod_f (fun i => Pr[Gi_prg i]) Gi_Gi_plus_1_close numCalls).
  intuition.
Qed.

(* ------------------------------- *)

(* Backtracking resistance, using indistinguishability proof *)
(* this proof is invalid, see thesis for revised proof *)

(* Adversary, split into two *)
Parameter A1 : Comp nat.        (* currently unused *)
Parameter A2 : list (list (Bvector eta)) -> KV -> Comp bool.
(* Also the adversary is slightly different from the one above. How do we re-use the adv? *)

Definition G1_prg_original_dup : Comp bool := (* copy of G1_prg_original *)
  [k, v] <-$2 Instantiate;
  [bits, _] <-$2 oracleMap _ _ GenUpdate_original (k, v) maxCallsAndBlocks;
  A bits.

Definition G1_br_original : Comp bool :=
  (* blocksForEachCall <-$ A1; (* implicitly compromises after that # calls *) *)
  [k, v] <-$2 Instantiate;
  [bits, state'] <-$2 oracleMap _ _ GenUpdate_original (k, v) maxCallsAndBlocks;
  A2 bits state'.

(* real world -- v-update move equivalence. need to prove that we need UpdateV -- needs an extra game at end of v-update equiv proof *)
Definition G1_br : Comp bool :=
  (* blocksForEachCall <-$ A1; (* implicitly compromises after that # calls *) *)
  (* TODO: not using this parameter yet, implicitly compromise after max calls (hardcoded)*)
  [k, v] <-$2 Instantiate;
  [head_bits, state'] <-$2 GenUpdate_noV (k, v) numCalls;
  [tail_bits, state''] <-$2 oracleMap _ _ GenUpdate state' (tail maxCallsAndBlocks);
  (* again, don't need tail here *)
  (* v update moved to beginning of each GenUpdate *)
  [k', v'] <-2 state'';
  v'' <- f k' (to_list v');      (* update v *)
  A2 (head_bits :: tail_bits) (k', v''). 

(* in general, how do we relate different adversaries in FCF? *)

(* A2 still cannot distinguish *)
(* how do I reuse the previous work? it depended on the adversary result, it wasn't an equivalence rewriting on the inside two lines *)
(* how would i even do this proof from scratch? would have to prove that PRF -> RF and RF -> RB yield equivalence etc. for A2 bits (k, v') <-- state *)
(* also, what about the extra UpdateV probabilities? *)

(* we don't know that Pr[G1_br] == Pr[G1_prg_dup]; that would be like assuming the state gives the adversary no extra info, which is like assuming what we want to prove? *)
(* all of our proof about G1_prg depended on the *adversary*, not the computations (but maybe they should have). *)
(* can we do the PRF_Advantage step in G1_br and reuse the RF->RB work from G1_prg? need to rephrase in terms of PRF_Adversary *)
Definition G1_prg_dup : Comp bool := (* copy of G1_prg *)
  [k, v] <-$2 Instantiate;
  [head_bits, state'] <-$2 GenUpdate_noV (k, v) blocksPerCall;
  [tail_bits, _] <-$2 oracleMap _ _ GenUpdate state' (tail maxCallsAndBlocks);
  A (head_bits :: tail_bits).

Definition G2_prg_dup : Comp bool := (* copy of G2_prg *)
  bits <-$ compMap _ GenUpdate_rb maxCallsAndBlocks;
  A bits.

(* ideal world *)
(* 1a and 2: v ~ {0,1} -> f v ~ {0,1}? maybe assume it *)
(* or add an extra PRF_Advantage (random k -> f k v yields random v') *)
Definition G2_br : Comp bool :=
  [k, v] <-$2 Instantiate;
  bits <-$ compMap _ GenUpdate_rb maxCallsAndBlocks;
  A2 bits (k, v).

Lemma G2_prg_br_eq :
  Pr[G2_br] <= Pr[G2_prg_dup].
Proof.
  unfold G2_prg_dup, G2_br.
  unfold Instantiate.
  simplify.
  fcf_irr_l. unfold RndK. fcf_well_formed.
  simplify.
  fcf_irr_l. unfold RndV. fcf_well_formed.
  simplify.
  fcf_skip.
  unfold RndK, RndV in *.
  (* should A2 be somehow constructed from A? *)
  (* also this isn't necessarily true unless A2 is constructed from A. A2 could just do dumb things. certainly Pr[best A2] == Pr[best A] (actually could it improve the adversary to give it more randomness?? probably not, if you're giving it a constant amt) *)
  (* Print Notation (Pr [ _ ]). *)
Admitted.

(* 2 and 2a are clearly equivalent? (k,v) gives no information about bits, so remove k, v *)
(* this is where the indistinguishability proof ends -- don't know how to use this as an intermediate stage. is it possible to do G1_br ->(?) G1_prg -> G2_prg -> G2_br?
or somehow interleave so that we know the probability is "squeezed" to be small?
G1_br ->(?) G1_prg -> G2_br -> G2_prg *)

(* TODO other equivalence/bounding theorems *)

Theorem G1_G2_close_b2 :
  | Pr[G1_br_original] - Pr[G2_br] | <= (numCalls / 1) * Gi_Gi_plus_1_bound.
Proof.
  unfold G1_br.
  unfold G2_br.
Admitted.

(* ------------------------------- *)

  (* Notes on our proof: (might be outdated as of 1/1/16)

Show GenUpdate's output indistinguishable from the output of this version, with v updated first: 

  v' <- f k v;
  [bits, v''] <-2 Gen_loop k v' n;
  k' <- f k (v'' ++ zeroes);
  ret (bits, (k', v'')).

(won't be exactly the same since v is updated an extra time in the beginning (first call to GenUpdate) -- unless we have the 1st GenUpdate oracle not update the v at all, then change all GenUpdate oracles after the first one to update v in the first line, according to i in the ith game)

---

G1: (assume instantiate ideal), then the adversary can query Generate+Update as many times as they want. all are done with PRF.

G2: (assume instantiate ideal), then the adversary can query Generate+Update as many times as they want. all are done with random sampling.

P P P P P P
R R R R R R

Gi i: (assume instantiate ideal), then the adversary can query Generate+Update as many times as they want (q). the first i calls are done with random sampling, the rest are done normally, with PRF.

R R P P P P

Gi_0: the game as-is (PRF)

R R P P P P

in ith oracle call:
Gi_1: replace all calls to PRF, updating K with a random function 
      replace all calls to PRF, updating V with a random function 

R R F P P P

Gi_2: replace all calls to RF, updating K with randomly-sampled bits
      replace all calls to RF, updating V with randomly-sampled bits

R R R P P P

---

Oi: Generate+Update: modified version of PRG that does Generate n + Update with random sampling if < i, and PRF otherwise

G_i_si_close: 

Show
R R P P P P and
R R R P P P close
(there's no induction on q. we have that the ith oracle call uses the oracle with random bits, so just show that the (i+1)th oracle calls in G_i and G_{i+1} are close)

| Pr[G_i] - Pr[G_{i+1}] | <= PRF_advantage + Pr[collisions]
(note that the randomly sampled V is first updated AGAIN in the new version of GenUpdate)

Pr[collisions] = 
"probability that /given the maximum input size n to any call/, the RF will be called on two identical inputs within the same oracle call"

the RF used both within the Generate loop and outside to generate the key?
but K <- RF(K, V || 0x00) so there can't be any collision within this call? *)

(* ----------------------------------- *)
(* Scratch work section -- ignore *)

Parameter A_t : Bvector eta -> bool.

Definition g1_test :=
  x <-$ {0,1}^eta;
  ret (A_t x).

Definition g2_test :=
  x <-$ {0,1}^eta;
  ret (A_t x).

Theorem g1_g2_eq : Pr[g1_test] == Pr[g2_test].
Proof.
  unfold g1_test. unfold g2_test.
  comp_skip.
  (* this also works, but you don't have to translate to prhl *)
  (* not clear on exactly what comp_skip is doing *)
  (* fcf_to_prhl_eq. *)
  (* comp_skip. *)
Qed.

(* ------ *)
(* How to get the state from an OracleComp: need to fully apply it with type params, oracle, and initial state *)

(* Definition GenUpdate_oc_test (state : KV) (n : nat) : *)
(*   OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) := *)
(*   [k, v_0] <-2 state; *)
(*   v <--$ (OC_Query _ (to_list v_0)); (* ORACLE USE *) *)
(*   [bits, v'] <--$2 Gen_loop_oc v n; *)
(*   k' <--$ (OC_Query _ (to_list v' ++ zeroes)); (* ORACLE USE *) *)
(*   $ ret (bits, (k', v')). *)

Definition getState_test (n : nat) : Comp bool :=
  [k, v] <-$2 Instantiate;
  [x1, x2] <-$2 Gen_loop_oc v n _ _ rb_oracle nil; (* note here *)
  ret true.

Parameter v_0 : Blist.
Check (OC_Query _ Blist).       (* ? *)

Parameter v : Bvector eta.
Parameter n : nat.
Check (Gen_loop_oc v n).
(* Gen_loop_oc v n
     : OracleComp (list bool) (Bvector eta)
         (list (Bvector eta) * Bvector eta) *)

End PRG.