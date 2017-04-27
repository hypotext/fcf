Set Implicit Arguments.

Require Import fcf.FCF.
(* RndInList has a useful theorem (qam_count) about counting calls to an oracle. *)
Require Import fcf.RndInList.
Require Import fcf.HasDups.
Require Import fcf.CompFold.
Require Import fcf.PRF.
Require Import fcf.OracleHybrid.
Require Import List.
Require Import fcf.PRF_DRBG.        (* note: had to move PRF_DRBG into FCF dir for this *)
Require Import Coq.Program.Wf.
Require Import fcf.OracleCompFold.

Require Import fcf.Tactics.

(* Shortcuts for FCF tactics *)
(* TODO remove / inline these *)
Ltac fs := fcf_simp.
Ltac fif := fcf_inline_first.
Ltac s := simpl.
Ltac fsr := fcf_spec_ret.
Ltac fskip := fcf_skip.
Ltac simplify :=
  repeat (try simpl; try fcf_inline_first; try fcf_simp).

Ltac rewrite_r := apply comp_spec_symm; eapply comp_spec_eq_trans_l.
Ltac flip := apply comp_spec_symm.
Ltac prog_equiv := repeat (simplify; fcf_skip_eq); try simplify.

Ltac bv_exist := try apply oneVector.

Variable bve : Bvector 10.

(* Lemma demonstrating use of `bv_exist` ltac *)
Lemma fcf_skip_admits : forall (n m : nat),
  comp_spec eq
            (x <-$ {0,1}^n;
             ret x)
            (y <-$ {0,1}^n;
             z <-$ {0,1}^n;
             ret y).
Proof.
  intros.
  (* Set Printing All. *)
  simpl.
  fcf_skip; bv_exist.
  fcf_irr_r.
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

(* Spec says "V || 0x00"; here we will use a list of 8 bits of 0 (a byte) *)
Fixpoint replicate {A} (n : nat) (a : A) : list A :=
  match n with
  | O => nil
  | S n' => a :: replicate n' a
  end.


(* --- Begin my HMAC-DRBG spec --- *)
Section PRG.

  (* note: the domain of the f is now Blist, not an abstract D
the key type is now also Bvector eta, since HMAC specifies that the key has the same size as the output (simplified) *)
Variable eta : nat.
(* Definition eta:=256%nat. *) (* coq gets stuck on an fcf_skip around line 256 *)

(* Variable RndK : Comp (Bvector eta). *)
(* Variable RndV : Comp (Bvector eta). *)
(* TODO replace them *)
Definition RndK : Comp (Bvector eta) := {0,1}^eta.
Definition RndV : Comp (Bvector eta) := {0,1}^eta.

Ltac kv_exist := try apply (oneVector eta, oneVector eta).

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

Lemma wf_instantiate : well_formed_comp Instantiate.
Proof. unfold Instantiate. fcf_well_formed. unfold RndK. fcf_well_formed.
       unfold RndV. fcf_well_formed. Qed.
Ltac wfi := apply wf_instantiate.

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
(*Fixpoint replicate {A} (n : nat) (a : A) : list A :=
  match n with
  | O => nil
  | S n' => a :: replicate n' a
  end.*)

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
(* Old version: did not update v *)
(* Definition GenUpdate_rb_intermediate (state : KV) (n : nat) *)
(*   : Comp (list (Bvector eta) * KV) := *)
(*   bits <-$ Gen_loop_rb n; *)
(*   ret (bits, state). *)

(* New version: updates state vector v to be the last element of bits. Doesn't matter b/c all bits sampled randomly unless n=0 *)
(* New new version: exactly like GenUpdate but with f replaced by uniform random sampling *)
(* needs this for the proof of Gi_normal_rb_eq *)
Definition GenUpdate_rb_intermediate (state : KV) (n : nat)
  : Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  v' <-$ {0,1}^eta;
  [bits, v''] <-$2 Gen_loop_rb_intermediate k v' n;
  ret (bits, (k, v'')).

Definition GenUpdate_rb_oracle (tt : unit) (n : nat) : Comp (list (Bvector eta) * unit) :=
  bits <-$ Gen_loop_rb n;
  ret (bits, tt).

Definition GenUpdate_rb (n : nat) : Comp (list (Bvector eta)) :=
  bits <-$ Gen_loop_rb n;
  ret bits.

(* TODO: prove well_formed for the oracles *)


(* oracleMap hardcodes acc for compFold as nil, so generalize it *)
(*LENB: moved HERE to REMOVE DEPENDENCE ON Hypothesis H_numCalls : numCalls > 0*)
Theorem compFold_acc blocksPerCall: forall numCalls bits acc state,
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
  induction numCalls; intros.
  - simpl. fcf_spec_ret.
  - simpl.
    fcf_inline_first. fcf_skip.
    remember a0 as bits1. remember b as state'. clear Heqbits1 Heqstate'.
    fcf_simp.
    apply IHnumCalls. 
Qed.
Theorem comp_spec_acc_2  blocksPerCall: forall numCalls acc k v,
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
  induction numCalls; intros.
  * simpl. fcf_spec_ret.
  * simpl.
    fcf_inline_first. fcf_simp. apply IHnumCalls.
Qed.

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

(* oracleMap hardcodes acc for compFold as nil, so generalize it 
LENB: MOVE UP, AND SIMPLIFIED PROOF
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
Qed. *)

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
(*LENB: MOVED UP
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
Qed.*)

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
(*LENB: if I don't move the definition of comp_spec_acc_2 up, I get 
  "Error: comp_spec_acc_2 depends on the variable H_numCalls which is not declared in the context." here*)

    - fcf_simp. simpl in *. subst. fcf_reflexivity.
Qed.

(* End proofs of v-update equivalence *)
(* ------------------------------------------------ *)

(* TODO: intermediate games with random functions and random bits *)

(* proving Pr[G2_prg'] == Pr[G2_prg''] could be hard (new intermediate game) *)

Definition G2_prg'' : Comp bool :=
  kv <-$ Instantiate;           (* OK to instantiate them? *)
  [bits, _] <-$2 oracleMap _ _ GenUpdate_rb_intermediate kv maxCallsAndBlocks;
  A bits.

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

Lemma oracleMap_v_sampling_eq : forall blocks k v init tt',
   comp_spec (fun x y => fst x = fst y)
      (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) unit_EqDec)
        (fun (acc : list (list (Bvector eta)) * unit) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ GenUpdate_rb_oracle s d;
         [r, s0]<-2 z; ret (rs ++ r :: nil, s0)) (init, tt') blocks)
      (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) eqDecState)
        (fun (acc : list (list (Bvector eta)) * KV) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ GenUpdate_rb_intermediate s d;
         [r, s0]<-2 z; ret (rs ++ r :: nil, s0)) (init, (k,v)) blocks).
Proof.
  induction blocks as [ | block blocks']; intros.
  - simplify. fcf_spec_ret.
  - fcf_skip; kv_exist.
    instantiate (1 := (fun x y => fst x = fst y)).
    {
      unfold GenUpdate_rb_oracle. simplify.
      fcf_irr_r.
      simplify.
      fcf_skip; kv_exist.
      (* this goes thru without needing the non-0 block hypothesis *)
      { instantiate (1 := (fun x y => x = fst y)).
        clear H H0.               (* ok? *)
        revert block k b.
        induction block as [ | n']; intros.
        - Print Gen_loop_rb_intermediate.
          simpl. fcf_spec_ret.
        - simpl. fcf_skip_eq. fcf_skip. simplify. fcf_spec_ret.
      }
      simpl in *. destruct b0. simpl in *. subst.
      simplify. fcf_spec_ret.
    }
    simpl in *. destruct b0. simpl in *. subst. fold compFold.
    simplify.
    destruct k0.
    destruct b.
    apply IHblocks'.
Qed.

(* This intermediate game isn't strictly necessary--G2_prg' is also an acceptable definition for the final game.
If we wanted to go with that definition, we would simply replace G2_prg with G2_prg' everywhere *)
Lemma G2_oracle_eq_v_sampling :
  Pr[G2_prg'] == Pr[G2_prg''].
Proof.
  unfold G2_prg', G2_prg''.
  unfold oracleMap.
  fcf_to_prhl_eq.
  fcf_irr_r. wfi.
  fcf_skip.
  destruct b.
  eapply oracleMap_v_sampling_eq.
  simplify. simpl in *. subst.
  fcf_ident_expand_l. fcf_ident_expand_r. fcf_skip.
Qed.

(* Relate Gen_loop_rb_intermediate (newly being used) with Gen_loop_rb *)
Lemma Gen_loop_rb_and_intermediate_eq : forall (n : nat) (k v : Bvector eta),
  comp_spec (fun x y => fst x = y) (Gen_loop_rb_intermediate k v n) (Gen_loop_rb n).
Proof.
  induction n as [ | n']; intros; simpl.
  - fcf_spec_ret.
  - fcf_skip_eq. fcf_skip. fcf_spec_ret.
Qed.

(* TODO use the correct theorem to flip sides *)
Lemma Gen_loop_rb_and_intermediate_eq2 : forall (n : nat) (k v : Bvector eta),
  comp_spec (fun x y => x = fst y) (Gen_loop_rb n) (Gen_loop_rb_intermediate k v n).
Proof.
  induction n as [ | n']; intros; simpl.
  - fcf_spec_ret.
  - fcf_skip_eq. fcf_skip. fcf_simp. fcf_spec_ret.
Qed.

(* pull it out? *)
Lemma length_replicate : forall {A : Type} (n : nat) (x : A),
    length (replicate n x) = n.
Proof.
  induction n; intros.
  * reflexivity.
  * simpl. rewrite IHn. reflexivity.
Qed.  

Open Scope nat.
(* oraclemap with intermediate rb is same as oi_prg with i = numcalls *)
Lemma oracleMap_rb_eq : forall calls k v res n,
    n + length calls = numCalls ->
   comp_spec
     (fun (x : list (list (Bvector eta)) * KV)
        (y : list (list (Bvector eta)) * (nat * KV)) => 
      fst x = fst y)
     (compFold (pair_EqDec (list_EqDec (list_EqDec eqdbv)) eqDecState)
        (fun (acc : list (list (Bvector eta)) * KV) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ GenUpdate_rb_intermediate s d;
         [r, s0]<-2 z; ret (rs ++ r :: nil, s0)) (res, (k, v))
        calls)
     (compFold
        (pair_EqDec (list_EqDec (list_EqDec eqdbv))
           (pair_EqDec nat_EqDec eqDecState))
        (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ Oi_prg numCalls s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (res, (n, (k, v))) calls).
Proof.
  induction calls as [ | call calls']; intros.
  - simplify. fcf_spec_ret.
  - (* v-sampling *)
    Opaque GenUpdate_rb_intermediate.
    simplify. simpl in *.
    fcf_skip_eq; kv_exist.
    destruct (lt_dec n (n + S (length calls'))).
    Focus 2. omega.
    + Transparent GenUpdate_rb_intermediate.
      repeat (simplify; fcf_skip_eq; simplify).
    + simplify. destruct b.
      eapply IHcalls'.
      omega.
Qed.    
Close Scope nat.

(* G2 is equal to last hybrid *)
(* should be even easier than G1 since no GenUpdate_noV happening? Wrong *)
Lemma G2_Gi_n_equal :
  Pr[G2_prg] == Pr[Gi_prg numCalls].
Proof.
  Print G2_prg.
  rewrite G2_oracle_eq.
  rewrite G2_oracle_eq_v_sampling.
  fcf_to_prhl_eq.
  unfold G2_prg''.
  unfold Gi_prg.
  fcf_skip_eq. simplify.

  rename b into k. rename b0 into v.
  fcf_skip.
  instantiate (1 := (fun x y => fst x = fst y)).

  (* note: switching between windows is C-x o *)
  - unfold oracleMap.
    apply oracleMap_rb_eq.
    simpl.
    unfold maxCallsAndBlocks.
    apply length_replicate.

  - simpl in *. subst.
    simplify. fcf_reflexivity.
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
(* old version *)
(* Definition GenUpdate_rb_intermediate_oc (state : KV) (n : nat)  *)
(*   : OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) := *)
(*   bits <--$ $ Gen_loop_rb n;    (* promote comp to oraclecomp, then remove from o.c. *) *)
(*   $ ret (bits, state). *)

(* @v new version: uses last v and updates (k,v) anyway *)
Definition GenUpdate_rb_intermediate_oc (state : KV) (n : nat) 
  : OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  v' <--$ $ {0,1}^eta;
  [bits, v''] <--$2 $ Gen_loop_rb_intermediate k v' n;    (* promote comp to oraclecomp, then remove from o.c. *)
  $ ret (bits, (k, v'')).

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
w    RB  RB  RF
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
  (*specialize (skipn_length' n l). intros.*)
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
(* the oracles don't matter (for those two specific oracles) *)
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
    fcf_skip; kv_exist.

    { instantiate (1 := (fun x y => fst x = fst y)).
      destruct (lt_dec init (init + S (length calls'))).
      * unfold GenUpdate_rb_intermediate_oc.
        simpl.
        fcf_inline_first.
        fcf_skip; kv_exist.
        simplify.
        fcf_skip_eq; kv_exist.
        simplify.
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
i just need an upper bound.
can i just say, there exists some i for which PRF_Advantage_Game i is >= all others?? by properties of rational numbers? otherwise, contradiction. i think i can't actually do this in coq. *)
(* also is this lemma actually true?? *)
Lemma PRF_Advantages_same : forall (i j : nat),
    i <> numCalls -> j <> numCalls ->
    PRF_Advantage_Game i == PRF_Advantage_Game j.
Proof.
  intros i j i_neq j_neq.
  unfold PRF_Advantage_Game. unfold PRF_Advantage.

  (* do i need this lemma? maybe there's an easier way *)
  (* i don't want to prove anything about differences in probability. *)
  (* should i use identical until bad? i'm not sure if such a bad event exists, since PRF is totally opaque *)
(* split the absolute values the other way *)
  (* proof by contradiction? *)
  (* or i could prove a bunch of game equivalences on the first two and the last two, massaging them to look like each other (removing the extraneous RB and PRF), so then it would look like |a-b| == |a-b| *)
  (* what I really want to prove is: 
forall i, i <> numCalls -> 
PRF_Advantage_Game i = PRF_Advantage (the normal one with just the PRF/RF difference) 

(might have a special case for i=0) *)
  (* also i should look at the lemma before this and make sure it's true *)
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
    (* this is actually not true and the whole strategy is not true *)
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

(* I guess this should be `exists i`, not `forall i` *)
Lemma Gi_prf_rf_close : forall (i : nat),
  | Pr[Gi_prf i] - Pr[Gi_rf i] | <= PRF_Advantage_i. (* this is the prf advantage for game 0, but should be `exists i` *)
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

Open Scope nat.

(* These examples take a long time to check because of `simplify`. Commented out for now. *)

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
(* not used anywhere *)
Admitted.

(* new postcondition *)
Definition bitsVEq {A B : Type} (x : A * (nat * KV)) (y : A * (nat * KV) * B) :=
  let (bits_x, state_x) := x in
  let (calls_x, kv_x) := state_x in
  let (k_x, v_x) := kv_x in

  let (bits_y, state_y) := fst y in
  let (calls_y, kv_y) := state_y in
  let (k_y, v_y) := kv_y in
  (* no statement about keys being equal for now *)
  bits_x = bits_y /\ v_x = v_y /\ calls_x = calls_y.

Ltac breakdown x := simpl in x; decompose [and] x; clear x; subst.

(* -------- *)
(* Rewrite gen_loop and updates computationally, and prove equivalence *)

Fixpoint Gen_loop_comp (k : Bvector eta) (v : Bvector eta) (n : nat)
  : Comp (list (Bvector eta) * Bvector eta) :=
  match n with
  | O => ret (nil, v)
  | S n' =>
    v' <- f k (to_list v);
    [bits, v''] <-$2 Gen_loop_comp k v' n';
    ret (v' :: bits, v'')
  end.

(* want to change to this, and prove the outputs are the same. 
the other GenUpdates don't use this version *)
Definition GenUpdate_comp (state : KV) (n : nat) :
  Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  v' <- f k (to_list v);
  [bits, v''] <-$2 Gen_loop_comp k v' n;
  k' <- f k (to_list v'' ++ zeroes);
  ret (bits, (k', v'')).

(* use this for the first call *)
Definition GenUpdate_noV_comp (state : KV) (n : nat) :
  Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  [bits, v'] <-$2 Gen_loop_comp k v n;
  k' <- f k (to_list v' ++ zeroes);
  ret (bits, (k', v')).

Lemma Gen_loop_comp_eq : forall n k v,
  comp_spec eq (ret (Gen_loop k v n)) (Gen_loop_comp k v n).
Proof.
  induction n as [ | n']; intros.
  - simpl. fcf_spec_ret.
  - simpl.
    unfold setLet.
    (* You need to apply your induction hypothesis to the first statement of the computation on the right.  The most direct way to do this is to explicitly apply transitivity: *)
    (* eapply comp_spec_eq_trans. *)
    Print comp_spec_eq_trans.
    eapply
      (@comp_spec_eq_trans _ _ 
           ((ret (let (bits, v'') := Gen_loop k (f k (to_list v)) n' in
                  (f k (to_list v) :: bits, v''))))

           (z <-$ ret Gen_loop k (f k (to_list v)) n';
            [bits, v'']<-2 z;
            ret (f k (to_list v) :: bits, v''))).
        
    comp_simp; reflexivity.
    comp_skip.
    (* this tactic will find the induction hypothesis and apply it *)
Qed.

Lemma Gen_loop_comp_eq_outer : forall n k v,
   comp_spec eq
     ([bits, v']<-2 Gen_loop k v n;
      ret (bits, (f k (to_list v' ++ zeroes), v')))
     (z <-$ Gen_loop_comp k v n;
      [bits, v']<-2 z; ret (bits, (f k (to_list v' ++ zeroes), v'))).
Proof.
  intros. 
  pose proof (Gen_loop_comp_eq n k v).
  eapply comp_spec_eq_trans.
  instantiate (1 := (z <-$ ret Gen_loop k v n;
         [bits, v'']<-2 z; ret (bits, (f k (to_list v'' ++ zeroes), v'')))).
  simplify. fcf_spec_ret.
  fcf_skip_eq.
Qed.

Lemma GenUpdate_comp_eq : forall n k v,
  comp_spec eq (GenUpdate (k,v) n) (GenUpdate_comp (k,v) n).
Proof.
  intros. simpl. unfold setLet. apply Gen_loop_comp_eq_outer.
Qed.

Lemma Gen_loop_oc_eq : forall n k v,
   comp_spec
     (fun (x : list (Bvector eta) * Bvector eta)
        (y : list (Bvector eta) * Bvector eta * unit) =>
      fst x = fst (fst y) /\ snd x = snd (fst y)) 
     (Gen_loop_comp k v n)
     ((Gen_loop_oc v n) unit unit_EqDec (f_oracle f eqdbv k) tt).
Proof.
  induction n as [ | n']; intros.
  - simplify. fcf_spec_ret.
  - simpl.
    unfold setLet.
    prog_ret_r.
    fcf_skip. fcf_simp. simpl in *. subst. fcf_spec_ret.
Qed.

(* ------- *)

(* second induction used to prove the lemma after it. calls = i, then destruct, the induction on calls > i *)
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
  Opaque Oi_prg. Opaque Oi_oc'.
  destruct l as [ | x xs]; intros.

  - simplify. fcf_spec_ret. simpl. repeat (split; auto).
    rewrite app_nil_r; reflexivity.
  -
    simplify.
    fcf_skip; kv_exist.
    instantiate (1 := (fun c d => bitsVEq c d
                                  /\ fst (snd c) = S i /\ fst (snd (fst d)) = S i
                                  (* keys become equal afterward on call i *)
                                  /\ fst (snd (snd c)) = fst (snd (snd (fst d))))).
    (* 1 call *)
    {
      Transparent Oi_prg. Transparent Oi_oc'.
      unfold Oi_prg. unfold Oi_oc'.
      simplify.
      (* casework on `i = 0`, `calls = i` and `calls > i` *)
      destruct (lt_dec i i). omega. 
      clear n.
      destruct (beq_nat i 0).
      -
        fcf_skip; kv_exist.
        instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd x = snd (fst y))).
        simpl. fcf_inline_first.
        eapply comp_spec_eq_trans_l.
        apply Gen_loop_comp_eq_outer.

        fcf_skip. 
        instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd x = snd (fst y))).
        (* induction *)
        apply Gen_loop_oc_eq.

        simplify. simpl in H1. breakdown H1. fcf_spec_ret.
        simplify. simpl in H1. breakdown H1. fcf_spec_ret.
        simpl. destruct k. auto.

      - Opaque GenUpdate.
        simpl.
        assert (beq_nat i i = true) by apply Nat.eqb_refl.
        destruct (beq_nat i i).
        Focus 2. inversion H.
        clear H.
        fcf_skip; kv_exist.
        instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd x = snd (fst y))).
        Transparent GenUpdate. unfold GenUpdate. unfold GenUpdate_oc.
        simpl. unfold setLet. prog_ret_r.
        eapply comp_spec_eq_trans_l.
        apply Gen_loop_comp_eq_outer.        
        fcf_skip. 

        (* induction *)
        apply Gen_loop_oc_eq.

        simplify. simpl in H1. breakdown H1. fcf_spec_ret.
        simplify. simpl in H1. breakdown H1. fcf_spec_ret.
        simpl. destruct k. auto.
        Opaque Oi_prg. Opaque Oi_oc'.
    }

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
      + simplify.
        fcf_skip; kv_exist.

        (* one call with calls > i (calls = S i) *)
        instantiate (1 := (fun c d => bitsVEq c d
                                      (* calls incremented by one *)
                                      /\ fst (snd c) = S calls
                                      /\ fst (snd (fst d)) = S calls
                                      (* keys equal *)
                                      /\ fst (snd (snd c)) = fst (snd (snd (fst d))))).
        {
          Transparent Oi_prg. Transparent Oi_oc'.
          unfold Oi_prg. unfold Oi_oc'.
          (* calls > i implies S calls != i *)
          assert (H_false : beq_nat (S calls) i = false).
          { apply Nat.eqb_neq. omega. }
          destruct (beq_nat (S calls) i). inversion H_false.
          clear H_false.
          simplify.
          destruct (lt_dec calls i). omega. (* contradiction *)
          apply not_lt in n.
          assert (beq_nat calls 0 = false).
          { apply Nat.eqb_neq. omega. }
          rewrite H0. Opaque GenUpdate.
          simpl.
          assert (beq_nat calls i = false).
          { apply Nat.eqb_neq. omega. }
          rewrite H1.
          Transparent GenUpdate. simpl. fcf_inline_first.
          fcf_skip; kv_exist.
          instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd x = snd (fst y))).
          fcf_simp. 
          fcf_spec_ret.
          simplify. simpl in *. breakdown H4. fcf_spec_ret.
          simpl. destruct k. auto.
          Opaque Oi_prg. Opaque Oi_oc'.          
        }

        simpl in H2. destruct b0. destruct b. destruct p. destruct p. destruct k. simpl in *. breakdown H2.
        simplify.
        
        eapply comp_spec_eq_trans_r. 
        eapply H; omega.
        
        (* now prove oracleCompMap_inner's eq *)
        { instantiate (1 := k1). 
          fcf_skip_eq; kv_exist.
          simplify. fcf_spec_ret.
          f_equal. f_equal.
          rewrite <- app_cons_eq.
          reflexivity.
        }
    }
Qed.

Theorem Gen_loop_rb_intermediate_keys_diff : forall (n : nat) (k1 k2 v : Bvector eta),
   comp_spec eq (Gen_loop_rb_intermediate k1 v n) (Gen_loop_rb_intermediate k2 v n).
Proof.
  induction n as [ | n']; intros; simpl.
  - fcf_spec_ret.
  - fcf_skip. fcf_skip.
Qed.

Theorem Gi_normal_prf_eq_compspec :
  forall (l : list nat) (i calls : nat) (k1 k2 v : Bvector eta) init,
    calls <= i ->

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
      fcf_skip; kv_exist.
      (* strengthen postcondition so we can prove calls < i -> S calls <= i to apply IHxs *)
      (* also strengthen it again because if calls < i then the keys must still be the same *)
      instantiate (1 := (fun c d => bitsVEq c d
                                    (* calls incremented by 1 *)
                                    /\ fst (snd c) = S calls /\ fst (snd (fst d)) = S calls
                                    (* output keys are the input keys *)
                                    (* /\ fst (snd (snd c)) = fst (snd (snd (fst d))) )). *)
                                    /\ fst (snd (snd c)) = k1
                                    /\ fst (snd (snd (fst d))) = k2)).
      (* includes calls *)
      (* one call with linked keys TODO *)
      {
        Transparent Oi_prg. Transparent Oi_oc'.
        simpl.
        destruct (lt_dec calls i).
        Focus 2. omega.         (* contradiction *)
        clear l.                (* calls < i *)
        unfold GenUpdate_rb_intermediate.
        simplify.
        (* @v *)
        fcf_skip_eq; kv_exist.
        simplify.
        fcf_skip; kv_exist.
        apply Gen_loop_rb_intermediate_keys_diff.
        subst. simplify.
        fcf_spec_ret.
        unfold bitsVEq. simpl. auto.
      }

      (* use IH *)
      { simpl in H2. destruct b0. destruct b. destruct p. destruct p. destruct k. simpl in *.
        breakdown H2. 
        simplify.

        eapply comp_spec_eq_trans_r.
        eapply IHxs; omega. 

        (* now prove oracleCompMap_inner's eq *)
        { fcf_skip_eq; kv_exist.
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
    apply Gi_normal_prf_eq_calls_eq_i; omega.
Qed.
        
Transparent oracleMap.
Transparent oracleCompMap_inner.
Transparent Oi_prg.
Transparent Oi_oc'.

(* this moves from the normal adversary to the PRF adversary (which depends on the prev.) *)
(* Gi_prg 0: PRF PRF PRF PRF
   Gi_prf 0: PRF PRF PRF PRF
   Gi_prg 2: RB RB PRF PRF
   Gi_prf 2: RB RB PRF PRF *)
Lemma Gi_normal_prf_eq : forall (i : nat),
  Pr[Gi_prg i] == Pr[Gi_prf i].
Proof.
  intros.
  unfold Gi_prg.
  unfold Gi_prf.
  unfold PRF_Adversary.

  fcf_to_prhl_eq.
  unfold Instantiate.
  unfold oracleCompMap_outer.
  fcf_inline_first.

  unfold Instantiate.
  comp_skip.
  Opaque oracleMap.
  simpl.
  fcf_inline_first.

  unfold Instantiate.
  fcf_inline_first.
  fcf_irr_r. unfold RndK. fcf_well_formed.
  fcf_inline_first.
  comp_skip.
  fcf_simp.
  simpl.
  fcf_inline_first.
  fcf_skip.

  instantiate (1 := fun x y => bitsVEq x y).
  -
    Transparent oracleMap.
    pose proof Gi_normal_prf_eq_compspec as Gi_prf_compspec.
    unfold oracleMap.
    specialize (Gi_prf_compspec maxCallsAndBlocks i 0 b b0 b1 nil).
    eapply comp_spec_eq_trans_r.
    eapply Gi_prf_compspec; omega.
    simplify.
    fcf_ident_expand_r.
    fcf_skip_eq; kv_exist.

  - simplify.
    simpl in H6. destruct b3. destruct p. destruct k. breakdown H6.
    fcf_ident_expand_l.
    fcf_skip_eq.
    simplify.
    fcf_reflexivity.
Qed.

(* expose the bad event (dups) *)
Lemma Gi_rf_return_bad_eq : forall (i : nat),
    Pr[Gi_rf i] == Pr[x <-$ Gi_rf_bad i; ret fst x].
Proof.
  intros. (* over all i--could be hard? *)
  fcf_to_prhl_eq.
  unfold Gi_rf.
  unfold Gi_rf_bad.
  repeat (simplify; fcf_skip_eq).
  simplify. fcf_spec_ret.
Qed.

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

Lemma oracleCompMap_rf_oracle_irrelevance : forall blocks calls i k v state,
   comp_spec eq
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (calls, (k, v)) blocks) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv))
        (randomFunc ({ 0 , 1 }^eta) eqdbl) state)
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (calls, (k, v)) blocks) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) randomFunc_withDups state).
Proof.
  induction blocks as [ | block blocks']; intros.
  - simplify. fcf_spec_ret.
  - simplify. fcf_skip_eq; kv_exist.
    {
      destruct (beq_nat calls 0).
      + destruct (lt_dec calls i); repeat (simplify; fcf_skip_eq; kv_exist; simplify). fcf_spec_ret.
        admit.
        SearchAbout randomFunc_withDups.
        (* TODO import that fn from PRF_DRBG instead and weaken precondition for randomFunc_withDups_spec *)
        admit. (* didn't adam prove this? *)
      + destruct (lt_dec calls i); repeat (simplify; fcf_skip_eq; kv_exist; simplify). fcf_spec_ret.
        destruct (beq_nat calls i); repeat (simplify; fcf_skip_eq; kv_exist; simplify).
        admit.
        admit.
        admit.

        unfold GenUpdate_PRF_oc.
        fcf_inline_first.
        simplify.
        fcf_spec_ret.
    }
    simplify. destruct b0.
    fcf_skip_eq; kv_exist.
    simplify. fcf_spec_ret.
Qed.

Lemma Gi_rf_dups_return_bad_eq : forall (i : nat),
    Pr[x <-$ Gi_rf_bad i; ret fst x] == Pr[x <-$ Gi_rf_dups_bad i; ret fst x].
Proof.
  intros.
  fcf_to_prhl_eq.
  unfold Gi_rf_bad.
  unfold Gi_rf_dups_bad.
  repeat (simplify; fcf_skip_eq).
  apply oracleCompMap_rf_oracle_irrelevance.
Qed.

(* expose the bad event (dups) *)
Lemma Gi_rb_return_bad_eq : forall (i : nat),
    Pr[Gi_rb i] == Pr[x <-$ Gi_rb_bad i; ret fst x].
Proof.
  intros.
  fcf_to_prhl_eq.
  unfold Gi_rb.
  unfold Gi_rb_bad.
  repeat (simplify; fcf_skip_eq).
  simplify.
  fcf_spec_ret.
Qed.

(* ---------------------------------- *)
(* Assuming the Gi_normal_rb_eq stuff starts here *)

(* Used in the below proof: relates Gen_loop_rb_intermediate and Gen_loop_oc *)
Lemma Gen_loop_rb_intermediate_oc_related : forall (n : nat) (k v : Bvector eta) (rb_state : list (Blist * (Bvector eta))),
   comp_spec
     (fun (x : list (Bvector eta) * Bvector eta)
        (y : list (Bvector eta) * Bvector eta * list (Blist * Bvector eta)) =>
      fst x = fst (fst y) /\ snd x = snd (fst y))
     (Gen_loop_rb_intermediate k v n)
     ((Gen_loop_oc v n) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle rb_state).
Proof.
  induction n as [ | n']; intros; simplify.
  - fcf_spec_ret.
  - unfold rb_oracle. simplify. fcf_skip_eq. simplify. fold rb_oracle.
    fcf_skip. simpl in *. destruct b0. simpl in *. destruct p. simpl in *. subst.
    simplify. fcf_spec_ret.
Qed.

(*
(* second induction used to prove the lemma after it. calls = i, then destruct, the induction on calls > i *)
(* relates Oi_prg with Oi_oc' *)
Lemma Gi_normal_rb_eq_calls_eq_i : forall l k v i calls init rb_state,
    calls = i ->
    comp_spec
      (fun (x0 : list (list (Bvector eta)) * (nat * KV))
           (y : list (list (Bvector eta)) * (nat * KV) *
                list (Blist * Bvector eta)) => bitsVEq x0 y)
      (compFold
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                     (pair_EqDec nat_EqDec eqDecState))
         (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
            [rs, s]<-2 acc;
          z <-$ Oi_prg (S i) s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
         (init, (calls, (k, v))) l)
      (z <-$
         (oracleCompMap_inner
            (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                        (pair_EqDec nat_EqDec eqDecState))
            (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
            (calls, (k, v)) l) (list (Blist * Bvector eta))
         (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle rb_state;
       [bits, nkv, state']<-3 z;
       ret (init ++ bits, nkv, state')).
Proof.
  Opaque Oi_prg. Opaque Oi_oc'.
  destruct l as [ | x xs]; intros.

  - simplify. fcf_spec_ret. simpl. repeat (split; auto).
    rewrite app_nil_r; reflexivity.
  -
    simplify.
    eapply comp_spec_seq. admit. admit.
    (* avoid fcf_skip, it will subst calls = i, which i don't want to link *)

    (* when calls = i, one is Gen_loop_rb and the other is Gen_loop_oc using the rb_oracle *)
    instantiate (1 := (fun c d => bitsVEq c d
                                  /\ fst (snd c) = S i /\ fst (snd (fst d)) = S i
                                  (* keys become equal afterward on call i *)
                                  /\ fst (snd (snd c)) = fst (snd (snd (fst d))))).
    (* 1 call *)
    { subst.
      Transparent Oi_prg. Transparent Oi_oc'.
      unfold Oi_prg. unfold Oi_oc'.
      simplify.
      (* casework on `i = 0`, `calls = i` and `calls > i` *)
      destruct (lt_dec i i). omega. 
      clear n.
      destruct (lt_dec i (S i)).
      Focus 2. omega. clear l.
      destruct (beq_nat i 0).
      (* i = 0? shouldn't matter whether the v is updated an additional time in the latter *)
      -
        fcf_skip. admit. admit.
        instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd x = snd (fst y))).
        unfold GenUpdate_rb_intermediate. simplify. 
        fcf_skip.
        instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd x = snd (fst y))).
        apply Gen_loop_rb_intermediate_oc_related.
        (* Error: Impossible to unify
 "(list (Bvector eta) * Bvector eta * list (Blist * Bvector eta))%type" with
 "(list (Bvector eta) * Bvector eta)%type". *)
        simpl in H2. destruct b0. destruct p. simpl in *. inversion H2. subst.
        unfold rb_oracle. simplify.
        fcf_irr_r. simplify. fcf_spec_ret. simplify. f_equal.
        (* oops, k and b are not equal because k is re-sampled! that's fine. my other proof structure should deal with this problem *)
        admit.

        (* uh this case is Wrong. do i need that k and v are equal? ugh if it's rb oracle then GenUpdate_noV (or with V) oc does update the key. should I make GenUpdate_rb update the k,v? but then that breaks the assumption in the other proof that the k,v go thru unchanged. this is just a problem when calls = i 

both for i=0 and i<>0?
is there any way i can change the top-level theorem?
maybe they aren't the same, but they are indistinguishable if you skipped??
since the initial k,v are rand samp,
and the new k v are also rand samp
so i guess it's not WRONG, just hard
can i prove the first one (RB) with k,v going in rand samp is the same as rand sampling a key going into PRF?
do i even need this top-level theorem? or is there some easier thing to state
can i prove each (each what? at what level?) equiv to some intermediate computation?
might need to backtrack
maybe an oracle that does nothing when queried for k and v? but still generates bits? lol how would it know. i would have to modify Gen_loop_oc,GenUpdates, etc. to pass an "input tag." would break a lot of outer proofs.

unique: maybe it just does nothing for k' <-- query to_list v' ++ zeroes (since unique)
what about the v-updating?? the v is still updated (by the outer) t be the last v returned
maybe Gen_loop_rb can update the v too?? does that break other things? (e.g. PRF thm)
i think it's ok: calls < i: both RB, both update (tho i have to change Gen_loop_rb to keep track)
calls = i: 
  for PRF oracle, v going in are the same. for RB oracle, v is updated again w RB
calls > i: for PRFs, v going in are the same

does this break anything else? *)
        simplify. fcf_spec_ret. simpl in *. subst. destruct k0. auto.
        simpl in *. subst. auto.

        Opaque Oi_prg. Opaque Oi_oc'.
      -
        (* presumably now `i <> 0`? *)
        assert (H_i_eq : beq_nat i i = true) by apply Nat.eqb_refl.
        rewrite H_i_eq.
        fcf_skip. admit. admit.
        instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd x = snd (fst y))).
        unfold GenUpdate_rb_intermediate. simpl.
        unfold rb_oracle. fcf_irr_r. simplify. fold rb_oracle.

        fcf_skip. 
        (* same problem as above except now the k's going in are not equal *)
        instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd x = snd (fst y))).
        (* apply Gen_loop_rb_intermediate_oc_related. *)
        admit.

        simpl in H3. destruct b1. destruct p. simpl in *. destruct H3. subst.
        unfold rb_oracle. fcf_irr_r. simplify. fcf_spec_ret.
        simpl. admit.           (* TODO k's not eq *)

        simpl in H2. destruct b0. destruct p. simpl in *. breakdown H2.
        simplify. fcf_spec_ret. simpl. destruct k0. auto.
    }

    (* rest of calls -- induct on the new list *)
    { intros.
      simplify. simpl in *. destruct p0. destruct p. destruct k1. simpl in *. destruct k0. simpl in H2. decompose [and] H2.
      (* avoid using subst *)
      rewrite H5. rewrite H3. rewrite H7. rewrite H9. 
      assert (n_eq : n = n0) by omega.
      rewrite n_eq.
      clear H5 H3 H7 H9 H4 n_eq H calls H0 H1.
      rename n0 into calls.

      assert (H_calls : calls > i) by omega.
      rename b1 into k'. rename b2 into v'.
      clear k v H2 b b0 H6 rb_state x l n.
      revert init k' v' l0 i calls l1 H_calls.
      induction xs as [ | x' xs']; intros.

      (* xs = nil *)
      + simplify. fcf_spec_ret. simpl. repeat (split; auto).
      (* xs = x' :: xs', use IH *)
      + simplify.
        fcf_skip. admit. admit.

        (* one call with calls > i (calls = S i) *)
        (* PRF oracle only *)
        instantiate (1 := (fun c d => bitsVEq c d
                                      (* calls incremented by one *)
                                      /\ fst (snd c) = S calls
                                      /\ fst (snd (fst d)) = S calls
                                      (* KV equal *)
                                      /\ fst (snd (snd c)) = fst (snd (snd (fst d))))).
        {
          Transparent Oi_prg. Transparent Oi_oc'.
          unfold Oi_prg. unfold Oi_oc'. simplify.
          destruct (lt_dec calls (S i)). omega. (* calls > i, so ~(calls < S i) *)
          destruct (lt_dec calls i). omega.     (* calls > i, so ~(calls < i) *)
          assert (beq_nat calls 0 = false).
          { apply Nat.eqb_neq. omega. }
          rewrite H. Opaque GenUpdate.
          assert (beq_nat calls i = false).
          { apply Nat.eqb_neq. omega. }
          rewrite H0.
          Transparent GenUpdate.
          simplify.
          fcf_spec_ret. simpl. auto.
          Opaque Oi_prg. Opaque Oi_oc'.
        }

        simpl in H1. destruct b0. destruct b. destruct p. destruct p. destruct k. simpl in *.
        breakdown H1.
        simplify.
        
        eapply comp_spec_eq_trans_r.
        eapply IHxs'; omega.
        
        (* now prove oracleCompMap_inner's eq *)
        { fcf_skip_eq; kv_exist.
          simplify. fcf_spec_ret.
          f_equal. f_equal.
          rewrite <- app_cons_eq.
          reflexivity.
        }
    }
Qed.

Lemma Gi_normal_rb_eq_compspec : forall l k v i calls init rb_state,
    calls <= i ->               (* or calls < i? *)
    comp_spec
      (fun (x : list (list (Bvector eta)) * (nat * KV))
           (y : list (list (Bvector eta)) * (nat * KV) *
                list (Blist * Bvector eta)) => bitsVEq x y)

      (compFold
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                     (pair_EqDec nat_EqDec eqDecState))
         (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
            [rs, s]<-2 acc;
          z <-$ Oi_prg (S i) s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
         (init, (calls, (k, v))) l)

      ([acc', state'] <-$2
                      ((oracleCompMap_inner
                          (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                      (pair_EqDec nat_EqDec eqDecState))
                          (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
                          (calls, (k, v)) l) (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle rb_state);
       [bits, nkv] <-2 acc';
       ret (init ++ bits, nkv, state')).
Proof.
  induction l as [ | x xs]; intros.
  - simplify. fcf_spec_ret. simpl. rewrite app_nil_r. repeat (split; auto).
  - assert (H_ilen : calls < i \/ calls = i) by omega.
    destruct H_ilen.
    clear H.

    Opaque Oi_prg. Opaque Oi_oc'.
    simplify.
    fcf_skip. admit. admit.
    (* strengthen postcondition so we can prove calls < i -> S calls <= i to apply IHxs *)
    (* also strengthen it again because if calls < i then the keys must still be the same *)
    instantiate (1 := (fun c d => bitsVEq c d
                                  (* calls incremented by 1 *)
                                  /\ fst (snd c) = S calls /\ fst (snd (fst d)) = S calls
                                  (* output keys are the input keys *)
                                  /\ fst (snd (snd c)) = k
                                  /\ fst (snd (snd (fst d))) = k)).
    (* includes calls *)
    (* one call with linked keys TODO *)
    {
      Transparent Oi_prg. Transparent Oi_oc'.
      simpl.
      destruct (lt_dec calls i).
      Focus 2. omega.         (* contradiction *)
      clear l.                (* calls < i *)
      unfold GenUpdate_rb_intermediate.
      simplify.
      assert (H_calls_lt : calls < S i) by omega.
      destruct (lt_dec calls (S i)).
      Focus 2. omega. fcf_inline_first.
      fcf_skip_eq; kv_exist.
      simplify.
      fcf_spec_ret. simpl. auto.
      Opaque Oi_prg. Opaque Oi_oc'.
    }

    (* use IH *)
    { simpl in H2. destruct b0. destruct b. destruct p. destruct p. destruct k0. simpl in *.
      breakdown H2. 
      simplify.

      eapply comp_spec_eq_trans_r.
      eapply IHxs; omega. 
      instantiate (1 := l).
      (* now prove oracleCompMap_inner's eq *)
      { fcf_skip_eq; kv_exist.
        simplify.
        fcf_spec_ret. f_equal. f_equal. rewrite <- app_assoc. f_equal.
      }
    } 
    
    (* calls = i *)
    + clear IHxs.
      clear H.
      apply Gi_normal_rb_eq_calls_eq_i; omega.
Qed.

Lemma Gi_normal_rb_compspec_kv_i : forall l k v i calls init rb_state,
   comp_spec
     (fun (x0 : list (list (Bvector eta)) * (nat * KV))
        (y : list (list (Bvector eta)) * (nat * KV) *
             list (Blist * Bvector eta)) => x0 = fst y)
     (z <-$ Instantiate;
      [k0, v0]<-2 z;
      z0 <-$
      compFold
        (pair_EqDec (list_EqDec (list_EqDec eqdbv))
           (pair_EqDec nat_EqDec eqDecState))
        (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
         [rs, s]<-2 acc;
         z0 <-$ Oi_prg (S i) s d; [r, s0]<-2 z0; ret (rs ++ r :: nil, s0))
        (init, (calls, (k0, v0))) l; ret z0)
     (z <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (calls, (k, v)) l) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle rb_state;
      [bits, nkv, state']<-3 z;
      ret (init ++ bits, nkv, state')).
Proof.
  Opaque Oi_prg. Opaque Oi_oc'.
  destruct l as [ | x xs]; intros.

  - simplify. fcf_irr_l. admit. simplify. fcf_spec_ret.
    (* base case not true again *)
Admitted.

Lemma twice_sample :
  comp_spec eq
            (x <-$ {0,1}^eta; x <-$ {0,1}^eta; ret x)
            (x <-$ {0,1}^eta; ret x).
Proof. fcf_irr_l. Qed.

Lemma Gi_normal_rb_eq_compspec_kv_inner : forall l k v i calls init rb_state,
    calls <= i ->
    comp_spec
      (fun (x : list (list (Bvector eta)) * (nat * KV))
           (y : list (list (Bvector eta)) * (nat * KV) *
                list (Blist * Bvector eta)) => x = fst y)

      (z <-$ Instantiate;
       [k, v]<-2 z;
       z0 <-$
          compFold
          (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                      (pair_EqDec nat_EqDec eqDecState))
          (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
             [rs, s]<-2 acc;
           z0 <-$ Oi_prg (S i) s d; [r, s0]<-2 z0; ret (rs ++ r :: nil, s0))
          (init, (calls, (k, v))) l;
       ret z0)

      ([acc', state'] <-$2
                      (oracleCompMap_inner
                         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                     (pair_EqDec nat_EqDec eqDecState))
                         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
                         (calls, (k, v)) l) (list (Blist * Bvector eta))
                      (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle rb_state;
       [bits, nkv] <-2 acc';
       ret (init ++ bits, nkv, state')).
Proof.
(* TODO apply it correctly below *)
  (* z is irrelevant UNTIL calls = i... this could actually work? *)
  (* well no, if i skip, then i can't apply the thm that assumes the incoming ones are the same? so maybe i should leave instantiate in?
no, the theorem wouldn't be in the right form...
can i add another instantiate line to skip???
is there some way to re-add a line of code after skipping it?? *)
  (* will it break things if i only add re-sampling on the *S i*th call of RB?? *)
  (* well that would be the ith call in PRF theorem... so yes *)
  induction l as [ | x xs]; intros.
  - fcf_irr_l. admit.
    SearchAbout (In _ _ -> comp_spec _ _ _ -> comp_spec _ _ _).
    simplify. fcf_spec_ret.
(* base case not true, kv not equal for any number of calls ... but we don't need that in the postcondition anyway *)
    (* do we need that in the post. for calls = i? for calls >= i? well we can strengthen that post and prove that that implies this *)
    admit.
  -
    assert (H_ilen : calls < i \/ calls = i) by omega.
    destruct H_ilen.
    clear H.

    (* calls < i, rb only *)
    + simplify.
      fcf_irr_l. admit.
(* this is true, kv not used or changed *)
      admit.

    (* calls = i *)
    +
      (* ok we have Instantiate here! destruct and induct...could work?? if i can figure out how to swap inside the program... *)
      
Admitted.

Parameter kvt : KV.

Lemma Gi_normal_rb_eq_compspec_kv : forall (l : list nat) (i calls : nat) (init : list (list (Bvector eta))) (rb_state : list (Blist * Bvector eta)),
    calls <= i ->
    comp_spec eq
     (* (fun (x : list (list (Bvector eta)) * (nat * KV)) *)
     (*    (y : list (list (Bvector eta)) * (nat * KV)) => *)
     (*    x = y) *)

     (z <-$ Instantiate;
      [k, v]<-2 z;
      z0 <-$
      compFold
        (pair_EqDec (list_EqDec (list_EqDec eqdbv))
           (pair_EqDec nat_EqDec eqDecState))
        (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
         [rs, s]<-2 acc;
         z0 <-$ Oi_prg (S i) s d; [r, s0]<-2 z0; ret (rs ++ r :: nil, s0))
        (init, (calls, (k, v))) l; ret z0)
     (* (ret (nil, nil)). *)
     (* (ret (nil, (O, kvt))) *)

     (a <-$ Instantiate;
      z0 <-$ ret (a, rb_state);
      [z, rb_state]<-2 z0;
      [k, v]<-2 z;
      z1 <-$
       (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv))
         (Oi_oc' i)
         (calls, (k, v)) l) _ _ rb_oracle rb_state;
      [res, _]<-2 z1;
      [bits, nkv] <-2 res;
      ret (init ++ bits, nkv)).
        (* (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv)) *)
        (* rb_oracle rb_state). *)
Proof.
  intros.
  induction l as [ | x xs]; intros.
  (* problem is that induction doesn't work in THIS form -- unless we can manipulate the induction hypothesis to show that comp_spec _ _ _ -> comp_spec _ _ _ (with stuff skipped?) 

but we have to induct in this form...??? *)
  (* because if we destruct (calls <= i) outside the induction, then we have to induct for calls < i, and that doesn't maintain the inductive invariant. calls may = i, and we don't have the Instantiates anymore *)

  (* do we even need calls <= i? we only needed it for the prev thm? *)
  (* can we do destruct, <something else>, induct? *)

  (* but CAN we induct in this form? k,v,etc aren't generalized :/ doesn't work for any k,v (tho they are in the support etc). not sure if IH will apply,
and if so, will this theorem itself apply correctly at the top level *)
  (* can i maybe add an extra instantiate somewhere... *)
  (* can i add a more clever postcondition *)
  (* have no idea how to manip comp_spec in assumptions *)
  (* if I just started from `calls = i` with one instantiate, i wouldn't have a problem, since i would destruct the list and reason about the first call, then go w calls > i *)
  (* can i add an assumption or precondition instead? *)
  (* can i prove a program equivalence w instantiate moved inside? or just a program equivalence/intermediate stage *)
  (* well i can't actually swap it inside since we compFold with (k,v)... *)
  (* can i destruct `calls <= i-1`? *)
  (* can i do cases `calls <= i-1`, `calls >= i-1`? then destruct TWICE (skipping differently each time) and induct?
destruct ->
for the first one: calls <= i-1 -> induct -> destruct: calls <= i-1 (still holds) or calls = i-1 ... what do i do here? induction hypothesis doesn't hold

the problem is that no matter what i do in the first case, i'm going to have to move into the second case w the Instantiates already used
is there any way i can make the first case self contained?
can i just not have cases? *)

(* is there any way i can say
(calls >= i -> comp_spec (stronger) ((k,v) <-$ Instantiate;c1) (c2))
->
(forall k v, In _ k -> In _ v -> calls = i -> (comp_spec (weaker) c1 c2)) *)

  - fcf_skip. admit. admit. simplify. fcf_spec_ret.
    rewrite app_nil_r. auto.

  (* have to do this inside the induction *)
 -  assert (H_ilen : calls < i \/ calls = i) by omega.
    destruct H_ilen.
    SearchAbout (In _ _ -> comp_spec _ _ _).
    SearchAbout (comp_spec _ _ _ -> comp_spec _ _ _).
  (* calls < i *)
  +
    (* input k and v are equal to RBs *)
    fcf_skip. admit. admit.
    simplify. 
    fcf_skip. admit. admit.
    instantiate (1 := (fun x y => x = fst y)).
    (* apply Gi_normal_rb_eq_compspec_kv_inner. *)

    admit.

    admit.

  (* calls = i *)
  +
    fcf_irr_r. (* KV on right get resampled *)
    admit.

    simplify.
    (* apply Gi_normal_rb_compspec_kv_i. *)

    admit.

Qed. *)

Print Oi_oc'.
Print GenUpdate_rb_intermediate_oc.
(* bits <--$ $ Gen_loop_rb n; $ ret (bits, state) *)

(* used in Oi_oc''. the difference between this function and GenUpdate_oc is that
it hardcodes the oracle to be RB oracle, and moves the k update to be the first line, 
rather than being after the bit generation, because k no longer depends on the new v *)
(* takes in key but doesn't use it, to match the type of other GenUpdates *)
Definition GenUpdate_oc_instantiate (state : KV) (n : nat) :
  OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) :=
  [k, v_0] <-2 state;
  k' <--$ $ {0,1}^eta;
  v <--$ $ {0,1}^eta;
  [bits, v'] <--$2 Gen_loop_oc v n;
  $ ret (bits, (k', v')).

(* used in Oi_oc''. the difference between this function and GenUpdate_rb_intermediate_oc
is that it now updates v (but still does not update k). 
why do we need to update v in the normal RB cases??? *)
(* okay, i see that we're trying to match the form of GenUpdate_oc_instantiate *)
(* at a high level, we're trying to bridge GenUpdate_oc_instantiate and GenUpdate_rb_intermediate_oc *)
(* now unused *)
Definition GenUpdate_rb_intermediate_oc_noV (state : KV) (n : nat) 
  : OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  
  [bits, v'] <--$2 $ Gen_loop_rb_intermediate k v n;    (* promote comp to oraclecomp, then remove from o.c. *)
  $ ret (bits, (k, v')).

(* does not carry the k state around *)
(* TODO: this function and the next theorem aren't used anywhere?? *)
Fixpoint Gen_loop_rb_intermediate_v (v : Bvector eta) (n : nat)
  : Comp (list (Bvector eta) * Bvector eta) :=
  match n with
  | O => ret (nil, v)
  | S n' =>
    v' <-$ {0,1}^eta;
    [bits, v''] <-$2 Gen_loop_rb_intermediate_v v' n';
    ret (v' :: bits, v'')
  end.

Lemma Gen_loop_rb_intermediate_nok_eq : forall k v x any_v,
    x <> 0 ->
    comp_spec eq (Gen_loop_rb_intermediate k v x)
              (Gen_loop_rb_intermediate_v any_v x).
Proof.
  destruct x as [ | x']; intros.
  - omega.
  - revert k v any_v.                           (* any_v is used here only *)
    induction x' as [ | x'']; intros.
    + simpl. fcf_skip_eq.
    + remember (S x'') as S_x''.
      simpl. fcf_skip_eq. fcf_skip.
Qed.

(* used in Oi_oc''. the difference between this function and GenUpdate_noV is that
1. we assume the oracle passed in is the RB oracle
2. because we make that assumption, k is independent of v, so we resample it
before the bits are generated (for ease of skipping) rather than after *)
(* note oracle state won't be the same as GenUpdate_noV_oc *)
Definition GenUpdate_noV_oc_k (state : KV) (n : nat) :
  OracleComp (list bool) (Bvector eta)  (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  k' <--$ $ {0,1}^eta;
  [bits, v'] <--$2 Gen_loop_oc v n;
  $ ret (bits, (k', v')).

Print Oi_oc'.
Print Gen_loop_oc.

(* (let GenUpdate_choose := *)
(*    if lt_dec callsSoFar i *)
(*    then GenUpdate_rb_intermediate_oc *)
(*    else *)
(*     if beq_nat callsSoFar 0 *)
(*     then GenUpdate_noV_oc *)
(*     else if beq_nat callsSoFar i then GenUpdate_oc else GenUpdate_PRF_oc in *)
(*  z <--$ GenUpdate_choose state n; *)
(*  [bits, state']<-2 z; $ ret (bits, (S callsSoFar, state'))) *)

(* hardcode oracle everywhere to be RB oracle *)
(* moves k sampling to the beginning of each relevant function *)
Definition Oi_oc'' (i : nat) (sn : nat * KV) (n : nat) 
  : OracleComp Blist (Bvector eta) (list (Bvector eta) * (nat * KV)) :=
  [callsSoFar, state] <-2 sn;
  let GenUpdate_choose :=
      if lt_dec callsSoFar i
      then GenUpdate_rb_intermediate_oc (* CHANGE: uses the last v *)
      else if beq_nat callsSoFar O
           then GenUpdate_noV_oc_k (* CHANGE: k pulled to beginning; does use last v *)
           else if beq_nat callsSoFar i (* callsSoFar = i *)
                then GenUpdate_oc_instantiate   (* CHANGE: kv pulled to beginning; does use last v *)
                else GenUpdate_PRF_oc in
  [bits, state'] <--$2 GenUpdate_choose state n;
    $ ret (bits, (S callsSoFar, state')).

(* uses genupdate rb on any call <= i *)
(* removes the extra k or k,v sampling before bit gen *)
Definition Oi_oc''' (i : nat) (sn : nat * KV) (n : nat) 
  : OracleComp Blist (Bvector eta) (list (Bvector eta) * (nat * KV)) :=
  [callsSoFar, state] <-2 sn;
  let GenUpdate_choose :=
      if lt_dec callsSoFar i
      then GenUpdate_rb_intermediate_oc
      else if beq_nat callsSoFar O
           then GenUpdate_rb_intermediate_oc_noV (* no k-sampling or v-sampling *)
           (* CHANGE: diff b/t GenUpdate_oc_k and this fn is, this one removes the k sampling before bit gen *)
           else if beq_nat callsSoFar i (* callsSoFar = i *)
                then GenUpdate_rb_intermediate_oc (* no k-sampling, only v-sampling *)
                (* diff b/t GenUpdate_oc_instantiate and this fn is, this one removes the k sampling before bit gen *)
                else GenUpdate_PRF_oc in
  [bits, state'] <--$2 GenUpdate_choose state n;
    $ ret (bits, (S callsSoFar, state')).


Lemma Gen_loop_oc_states_diff : forall x state2 state1 v ,
   comp_spec
     (fun
        x0 y : list (Bvector eta) * Bvector eta * list (Blist * Bvector eta) =>
      fst x0 = fst y)
     ((Gen_loop_oc v x) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state2)
     ((Gen_loop_oc v x) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state1).
Proof.
    induction x as [ | x']; intros; simplify.
    - fcf_spec_ret.
    - unfold rb_oracle. simplify. fold rb_oracle.
      fcf_skip_eq. simplify.
      fcf_skip. simplify. fcf_spec_ret.
      simpl in *. inversion H2. f_equal.
Qed.  

(* used below the below thm *)
Lemma GenUpdate_swap_k_loop_eq : forall state1 state2 k v x,
   comp_spec
     (fun x0 y : list (Bvector eta) * KV * list (Blist * Bvector eta) =>
      fst x0 = fst y)
     ((GenUpdate_noV_oc (k, v) x) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state1)
     ((GenUpdate_noV_oc_k (k, v) x) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state2).
Proof.
  intros.
  unfold GenUpdate_noV_oc.
  unfold GenUpdate_noV_oc_k.

  simplify.
  (* it's not updating the state?? probably bc i'm NOT using an oracle, just {0,1}^n? *)

  (* swap the k-sampling with gen_loop on the right *)
  rewrite_r.
  (* well, are the states going to be equal?? should i get rid of states first and add ANOTHER intermediate game? *)
  instantiate (1 :=
                 (* Check ( *)
                 (z1 <-$
                     (Gen_loop_oc v x) (list (Blist * Bvector eta))
                     (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state2;
                  a <-$ { 0 , 1 }^eta;
                  [z2, state3]<-2 z1;
                  ([bits, v']<-2 z2; $ ret (bits, (a, v'))) (list (Blist * Bvector eta))
                                                            (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state3)).
  {
    (* Print Ltac prog_swap_r. *)
    rewrite_r.
    instantiate (1 :=
                   (a <-$ { 0 , 1 }^eta;
                    z1 <-$
                       (Gen_loop_oc v x) (list (Blist * Bvector eta))
                       (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state2;
                    [z2, state3]<-2 z1;
                    ([bits, v']<-2 z2; $ ret (bits, (a, v'))) (list (Blist * Bvector eta))
                                                              (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state3)).
    eapply comp_spec_eq_swap.
    fcf_skip_eq; kv_exist. simplify.
    fcf_skip_eq. simplify. fcf_spec_ret.
  }

  fcf_skip. instantiate (1 := (fun x y => fst x = fst y)).
(*LENB AGAIN, some varibales not in scope*)
  apply Gen_loop_oc_states_diff.

  simplify. unfold rb_oracle. simplify. fcf_skip_eq. simplify. simpl in *. inversion H2. subst.
  fcf_spec_ret.
Qed.

(* similar to the above lemma, but w/ v-updates *)
Lemma GenUpdate_swap_k_loop_equiv_v_update : forall state1 state2 k v x,
   comp_spec
     (fun x0 y : list (Bvector eta) * KV * list (Blist * Bvector eta) =>
      fst x0 = fst y)
     ((GenUpdate_oc (k, v) x) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state1)
     ((GenUpdate_oc_instantiate (k, v) x) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state2).
Proof.
  intros.
  unfold GenUpdate_oc.
  unfold GenUpdate_oc_instantiate.
  simplify.

 (* swap the k-sampling under v-sampling and gen_loop on the right *)
  rewrite_r.
  (* well, are the states going to be equal?? should i get rid of states first and add ANOTHER intermediate game? *)
  instantiate (1 :=
                 (* Check ( *)
                 (res <-$ (v' <-$ {0,1}^eta;
                           z1 <-$
                              (Gen_loop_oc v' x) (list (Blist * Bvector eta))
                              (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state2;
                           ret (v', z1));
                  a <-$ { 0 , 1 }^eta;
                  [v', z1] <-2 res;
                  [z2, state3]<-2 z1;
                  ([bits, v']<-2 z2; $ ret (bits, (a, v'))) (list (Blist * Bvector eta))
                                                            (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state3)).
  {
    (* Print Ltac prog_swap_r. *)
    rewrite_r.
    instantiate (1 :=
                   (a <-$ { 0 , 1 }^eta;
                    res <-$ (v' <-$ {0,1}^eta;
                             z1 <-$
                                (Gen_loop_oc v' x) (list (Blist * Bvector eta))
                                (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state2;
                             ret (v', z1));
                    [v', z1] <-2 res;
                    [z2, state3]<-2 z1;
                    ([bits, v']<-2 z2; $ ret (bits, (a, v'))) (list (Blist * Bvector eta))
                                                              (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state3)).
    eapply comp_spec_eq_swap.
    fcf_skip_eq; kv_exist. simplify.
    fcf_skip_eq; kv_exist. simplify. fcf_skip_eq. simplify. fcf_spec_ret.
  }

  simplify. unfold rb_oracle. simplify. fold rb_oracle. fcf_skip_eq; kv_exist. simplify.
  fcf_skip; kv_exist.

  instantiate (1 := (fun x y => fst x = fst y)).
  apply Gen_loop_oc_states_diff.

  simpl in *. destruct b1. simpl in *. destruct p. inversion H2. subst.
  simplify. unfold rb_oracle. simplify. fcf_skip_eq. simplify.
  fcf_spec_ret.
Qed.

(* Oi_oc' to Oi_oc'' *)
Lemma oracleCompMap_rb_instantiate_inner : forall l i k v calls state1 state2,
    comp_spec (fun x y => fst x = fst y) (* rb state might not be equal *)
              ((oracleCompMap_inner
                  (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                              (pair_EqDec nat_EqDec eqDecState))
                  (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
                  (calls, (k, v)) l) (list (Blist * Bvector eta))
                                     (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state1)

              ((oracleCompMap_inner
                  (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                              (pair_EqDec nat_EqDec eqDecState))
                  (list_EqDec (list_EqDec eqdbv)) (Oi_oc'' i)
                  (* note the double prime here: this replaces OC_Query w Instantiate *)
                  (* also in GenUpdate_noV_oc_k the one k call is moved up *)
                  (calls, (k, v)) l) (list (Blist * Bvector eta))
                                     (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state2).
Proof.
  induction l as [ | x xs]; intros.
  - simplify; fcf_spec_ret.
  - simplify.
    (*  "(list (Bvector eta) * (nat * KV) * list (Blist * Bvector eta))%type" with
 "(list (Bvector eta) * KV * list (Blist * Bvector eta))%type". *)
    fcf_skip; kv_exist.
    (* might need casework on calls = i *)
    (* one call: Oi_oc' to Oi_oc'' *)
    +
      instantiate (1 := (fun x y => fst x = fst y)). (* rb state might not be equal *)
      simplify. Transparent Oi_oc'. Transparent Oi_oc''. simpl.
      destruct (beq_nat calls i).
      (* calls = i *)
      { destruct (lt_dec calls i).
        { (* calls < i *)
          simplify.
          fcf_skip; kv_exist.
          {
            simplify.
            fcf_skip; kv_exist.
            simplify.
            fcf_spec_ret.
            (* @v hey this works now due to the v-updating changing. also i started redoing the bottom cases *)
          }
        }
        (* calls >= i *)
        apply not_lt in n.
        destruct (beq_nat calls 0). 
        (* calls = 0 *)
        - apply GenUpdate_swap_k_loop_eq.
        - (* calls != 0 *)
          apply GenUpdate_swap_k_loop_equiv_v_update.
      } 
      (* calls != i *)
      { (* same computations, but with different rb_state *)
        (* fcf_skip; kv_exist. *)
        (* instantiate (1 := (fun c d => fst c = fst d)). *)
        {
          destruct (lt_dec calls i).
          - simplify. fcf_skip_eq; kv_exist. simplify.
            fcf_skip; kv_exist.
            simplify.
            fcf_spec_ret.
          - SearchAbout (beq_nat _ _).
            assert (beq_dec : calls = 0 \/ calls <> 0) by omega.
            destruct beq_dec as [beqtrue | beqfalse ].
            apply not_lt in n.
            apply beq_nat_true_iff in beqtrue.
            rewrite beqtrue.

            (* same case as above with k-sampling-swapping *)
             apply GenUpdate_swap_k_loop_eq.

            (* SearchAbout (beq_nat _ _). *)
            apply beq_nat_false_iff in beqfalse. rewrite beqfalse.
            simplify. fcf_spec_ret.
        } 

        (* simplify. fcf_spec_ret. simpl in *. inversion H1. subst. f_equal. *)
      } 
    + simpl in H1. destruct b0. destruct b1. destruct p. simpl in *. destruct k0. inversion H1. subst.
      fcf_skip; kv_exist.
      simplify.
      instantiate (1 := (fun x y => fst x = fst y)).
      fcf_spec_ret.
      (* apply IHxs. *) (* ??? *)

      simpl in H4. destruct b2. destruct p. destruct p. simpl in *. inversion H4. subst.
      simplify.
      fcf_skip. destruct k0. apply IHxs.
      simplify. simpl in *. destruct p. inversion H7. subst.
      fcf_spec_ret.
Qed.
(* note i switched the order of k and v in GenUpdate_oc_instantiate *)

Notation "A = B = C" := (A = B /\ B = C).

(* Oi_oc'' to Oi_oc''', case: calls > i *)
Lemma Oi_ocs_eq_calls_gt_i : forall l k v state1 state2 calls i,
    calls > i ->
   comp_spec (fun x y => fst x = fst y)
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc'' i) 
         (calls, (k, v)) l) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state1)
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
         (calls, (k, v)) l) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state2).
Proof.
  induction l as [ | x xs]; intros.
  - simplify. fcf_spec_ret.
  - simplify.
    destruct (lt_dec calls i). omega.
    assert (calls_neq_i : calls <> i) by omega.
    apply beq_nat_false_iff in calls_neq_i.
    rewrite calls_neq_i. 
    assert (calls_neq_0 : calls <> 0) by omega.
    apply beq_nat_false_iff in calls_neq_0.
    rewrite calls_neq_0.
    simplify. fcf_skip; kv_exist.
    simplify. simpl in *. destruct l1. destruct p. inversion H2. subst.
    fcf_spec_ret.
    destruct p. inversion H2. subst.
    fcf_spec_ret.
Qed.

(* Oi_oc'' to Oi_oc''', case: i = 0 *)
Lemma oracleCompMap_rb_instantiate_outer_i_eq_0 : forall l i state,
    beq_nat i 0 = true ->                                        (* separate theorem *)
    comp_spec (fun x y => fst (fst x) = fst (fst y)) (* weaker precondition--just k's equal? *)
              ([k, v] <-$2 Instantiate;
               a <-$
                 (oracleCompMap_inner
                    (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                (pair_EqDec nat_EqDec eqDecState))
                    (list_EqDec (list_EqDec eqdbv)) (Oi_oc'' i)
                    (* note Oi_oc': need to rewrite w first theorem in outer *)
                    (O, (k, v)) l) (list (Blist * Bvector eta))
                 (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
               ret a)
              ([k, v] <-$2 Instantiate;
               k <-$ RndK;    (* instead of Instantiate, to deal with noV *)
               a <-$
                 (oracleCompMap_inner
                    (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                (pair_EqDec nat_EqDec eqDecState))
                    (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
                    (O, (k, v)) l) (list (Blist * Bvector eta))
                 (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
               ret a).
Proof.
  intros.
  (* rename H into calls_leq_i. *)
  rename H into i_eq_0.
  (* swap kv in latter as in the mask thm above *)
  destruct l as [ | x xs].
  - simplify. unfold Instantiate. simplify. fcf_irr_r. unfold RndK. fcf_well_formed.
    simplify. rewrite_r.
    { instantiate
      (1 :=
         (k0 <-$ RndK;
          a <-$ RndV;
          z <-$ ret (b, a);
          [_, v]<-2 z;
          a0 <-$ (x <-$ ret (nil, (O, (k0, v))); ret (x, state)); ret a0)).
    fcf_swap fcf_right. fcf_skip_eq; kv_exist. fcf_skip_eq; kv_exist. simplify.
    fcf_spec_ret. }
    fcf_skip_eq; kv_exist. simplify. fcf_skip_eq; kv_exist. simplify. fcf_spec_ret.
  -
    (* calls = 0 and i = 0 *)
    Opaque Oi_oc''. Opaque Oi_oc'''.
    simplify.
    (* Skip the two initial Instantiates *)
    fcf_skip_eq; kv_exist. simplify.
    Transparent Oi_oc''. Transparent Oi_oc'''.
    simpl. apply beq_nat_true in i_eq_0. subst. simplify.
    (* GenUpdate_noV_oc_k is inlined in first, GenUpdate_rb_intermediate_oc_v in second *)
    Print GenUpdate_noV_oc_k.
    Print GenUpdate_rb_intermediate_oc. (* like the above but with no k sampling *)

    (* Skip the lined-up a-sampling (inline k-sampling) and k-sampling *)
    fcf_skip_eq; kv_exist.
    simplify. fcf_skip; kv_exist.

    (* Gen_loop_oc ~ Gen_loop_rb_intermediate *)
    { instantiate (1 := (fun x y => fst x = y)).
      revert b0 a state. induction x as [ | x']; intros.
      - simplify. fcf_spec_ret.
      - simplify. unfold rb_oracle. simplify. fold rb_oracle.
        fcf_skip_eq. fcf_skip. simplify. fcf_spec_ret.
    } 
    simpl in H1. destruct b3. inversion H1. subst.
    simplify. fcf_skip; kv_exist.

(* separate lemma for induction on rest of list, show calls > i *)
    { instantiate (1 := (fun x y => fst x = fst y)).
      apply Oi_ocs_eq_calls_gt_i; omega. }
    { simplify. simpl in H4. destruct p. inversion H4. subst. fcf_spec_ret. }
Qed.

Ltac rewrite_l := apply comp_spec_symm; eapply comp_spec_eq_trans_l.
  
(* this isn't actually used in the below thm because i can't get it to unify, so i inlined the proof *)
Lemma k_loop_swap_after : forall (i : nat) (xs : list nat)
                                 (state : list (Blist * Bvector eta)) (x : nat) (calls : nat) (k : Bvector eta),
   comp_spec eq
     (k0 <-$ RndK;
      a <-$
      (z0 <-$
       (z0 <-$
        (z0 <-$ (x0 <-$ { 0 , 1 }^eta; ret (x0, state));
         [z, s']<-2 z0;
         z1 <-$ (x0 <-$ Gen_loop_rb_intermediate k0 z x; ret (x0, s'));
         [z2, s'0]<-2 z1;
         ([bits, v'']<-2 z2; $ ret (bits, (k0, v'')))
           (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
           rb_oracle s'0);
        [z, s']<-2 z0;
        ([bits, state']<-2 z; $ ret (bits, (S calls, state')))
          (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
          rb_oracle s');
       [z, s']<-2 z0;
       ([res, state']<-2 z;
        z1 <--$
        oracleCompMap_inner
          (pair_EqDec (list_EqDec (list_EqDec eqdbv))
             (pair_EqDec nat_EqDec eqDecState))
          (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) state' xs;
        [resList, state'']<-2 z1; $ ret (res :: resList, state''))
         (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
         rb_oracle s'); ret a)

     (v' <-$ {0,1}^eta;
      res <-$ Gen_loop_rb_intermediate k v' x; (* k0,v0 are swapped after, so just use any k,v in env *)
      k0 <-$ RndK;
      [bits, last_bv] <-2 res;
      a <-$
        (oracleCompMap_inner
           (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                       (pair_EqDec nat_EqDec eqDecState))
           (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) (S calls, (k0, last_bv)) xs)
        (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
        rb_oracle state;
      a0 <-$
         ([z, s']<-2 a;
          ([resList, state'']<-2 z; $ ret (bits :: resList, state''))
            (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
            rb_oracle s'); ret a0).
Proof.
  intros.
  rewrite_l.
  instantiate (1 :=
    (inter <-$ (v' <-$ { 0 , 1 }^eta;
      res <-$ Gen_loop_rb_intermediate k v' x;
      ret (v', res));
      k0 <-$ RndK;
      [v', res] <-2 inter;
      [bits, last_bv]<-2 res;
      a <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i)
         (S calls, (k0, last_bv)) xs) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
      a0 <-$
      ([z, s']<-2 a;
       ([resList, state'']<-2 z; $ ret (bits :: resList, state''))
         (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
         rb_oracle s'); ret a0)).
  { simplify. fcf_skip_eq; kv_exist. simplify. fcf_skip_eq; kv_exist. simplify. fcf_skip_eq; kv_exist. }
  apply comp_spec_symm.

  rewrite_l.
  instantiate (1 :=
      k0 <-$ RndK;
     (inter <-$
      (v' <-$ { 0 , 1 }^eta;
       res <-$ Gen_loop_rb_intermediate k v' x; ret (v', res));
      (let '(_, (bits, last_bv)) := inter in
            a <-$
            (oracleCompMap_inner
               (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                  (pair_EqDec nat_EqDec eqDecState))
               (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i)
               (S calls, (k0, last_bv)) xs) (list (Blist * Bvector eta))
              (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
            a0 <-$
            ([z, s']<-2 a;
             ([resList, state'']<-2 z; $ ret (bits :: resList, state''))
               (list (Blist * Bvector eta))
               (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle s'); 
            ret a0))).
  { eapply comp_spec_eq_swap. }

  apply comp_spec_symm.

  (* now k is at the top of both *)
  fcf_skip_eq; kv_exist.
  simplify.
  fcf_skip_eq; kv_exist.
  simplify.
  fcf_skip_eq; kv_exist.

  { revert a a0 k.
    induction x as [ | x']; intros; simpl.
    - fcf_spec_ret. 
    - fcf_skip_eq. fcf_skip_eq. }

  simplify.
  fcf_skip_eq; kv_exist.
Qed.

(* Oi_oc'' to Oi_oc''', third (and last) case: calls <= i and i != 0 *)
(* states same or different? going to have same so i can do eq (diff might let IH apply) *)
Lemma oracleCompMap_rb_instantiate_outer_i_neq_0 : forall l calls i state,
    calls <= i ->
    beq_nat i 0 = false ->                                        (* separate theorem *)
    comp_spec (fun x y => fst (fst x) = fst (fst y)) (* weaker precondition *)
              ([k, v] <-$2 Instantiate;
               a <-$
                 (oracleCompMap_inner
                    (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                (pair_EqDec nat_EqDec eqDecState))
                    (list_EqDec (list_EqDec eqdbv)) (Oi_oc'' i)
                    (* note Oi_oc': need to rewrite w first theorem in outer *)
                    (calls, (k, v)) l) (list (Blist * Bvector eta))
                 (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
               ret a)
              ([k, v] <-$2 Instantiate;
               k <-$ RndK;
               a <-$
                 (oracleCompMap_inner
                    (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                (pair_EqDec nat_EqDec eqDecState))
                    (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
                    (calls, (k, v)) l) (list (Blist * Bvector eta))
                 (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
               ret a).
Proof.
  intros.
  rename H0 into i_neq_0.
  fcf_skip_eq; kv_exist. simplify.
  (* fcf_irr_r. wfi. simplify. *)
  (* calls < i: kv don't matter *)
  (* calls = i: there's an extra instantiate inside *)

  rename b into k. rename b0 into v.
  revert calls i state H k v i_neq_0.
  induction l as [ | x xs]; intros. (* there isn't an induction in the i_eq_0 version, only a destruct *)
  (* base case *)
  - fcf_irr_r. unfold RndK. fcf_well_formed. simplify. fcf_spec_ret.

  (* induction: l = x :: xs *)
  - assert (H_ilen : calls < i \/ calls = i) by omega.
    destruct H_ilen.
    clear H.

    (* calls < i: apply induction hypothesis *)
    (* maybe i don't need induction? induct separately on inside *)
    (* this case might be hard because I need to "push" the extra instantiate on the right inside *)

    + Opaque Oi_oc''. Opaque Oi_oc'''.
      simplify. Transparent Oi_oc''. simplify.
      (* intuitively, what should the calls < i proof look like? *)
      destruct (lt_dec calls i). Focus 2. omega.

      (* calls < i *)
      Transparent Oi_oc'''. simplify. destruct (lt_dec calls i). Focus 2. omega.
      simplify.

      rewrite_r.
      (* eapply k_loop_swap_after. *)
      instantiate (1 :=      (v' <-$ {0,1}^eta;
      res <-$ Gen_loop_rb_intermediate k v' x; (* k0,v0 are swapped after, so just use any k,v in env *)
      k0 <-$ RndK;
      [bits, last_bv] <-2 res;
      a <-$
        (oracleCompMap_inner
           (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                       (pair_EqDec nat_EqDec eqDecState))
           (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) (S calls, (k0, last_bv)) xs)
        (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
        rb_oracle state;
      a0 <-$
         ([z, s']<-2 a;
          ([resList, state'']<-2 z; $ ret (bits :: resList, state''))
            (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
            rb_oracle s'); ret a0)).

      (* eapply k_loop_swap_after. *)
      (* pose proof (k_loop_swap_after i xs state x calls k) as k_loop_swap_after_init. *)
      (* apply k_loop_swap_after_init. *)

      (* ------ *)
      (* INLINE k_loop_swap_after PROOF (because eapply above can't unify... *)

      {
        rewrite_l.
        instantiate (1 :=
                       (inter <-$ (v' <-$ { 0 , 1 }^eta;
                                   res <-$ Gen_loop_rb_intermediate k v' x;
                                   ret (v', res));
                        k0 <-$ RndK;
                        [v', res] <-2 inter;
                        [bits, last_bv]<-2 res;
                        a <-$
                          (oracleCompMap_inner
                             (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                         (pair_EqDec nat_EqDec eqDecState))
                             (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i)
                             (S calls, (k0, last_bv)) xs) (list (Blist * Bvector eta))
                          (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
                        a0 <-$
                           ([z, s']<-2 a;
                            ([resList, state'']<-2 z; $ ret (bits :: resList, state''))
                              (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                              rb_oracle s'); ret a0)).
        { simplify. fcf_skip_eq; kv_exist. simplify. fcf_skip_eq; kv_exist. simplify. fcf_skip_eq; kv_exist. }
        apply comp_spec_symm.

        rewrite_l.
        instantiate (1 :=
                       k0 <-$ RndK;
                     (inter <-$
                            (v' <-$ { 0 , 1 }^eta;
                             res <-$ Gen_loop_rb_intermediate k v' x; ret (v', res));
                      (let '(_, (bits, last_bv)) := inter in
                       a <-$
                         (oracleCompMap_inner
                            (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                        (pair_EqDec nat_EqDec eqDecState))
                            (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i)
                            (S calls, (k0, last_bv)) xs) (list (Blist * Bvector eta))
                         (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
                       a0 <-$
                          ([z, s']<-2 a;
                           ([resList, state'']<-2 z; $ ret (bits :: resList, state''))
                             (list (Blist * Bvector eta))
                             (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle s'); 
                       ret a0))).
        { eapply comp_spec_eq_swap. }

        apply comp_spec_symm.

        (* now k is at the top of both *)
        fcf_skip_eq; kv_exist.
        simplify.
        fcf_skip_eq; kv_exist.
        simplify.
        fcf_skip_eq; kv_exist.

        { revert a a0 k.
          induction x as [ | x']; intros; simpl.
          - fcf_spec_ret. 
          - fcf_skip_eq. fcf_skip_eq. }

        simplify.
        fcf_skip_eq; kv_exist.
      }

      (* END SWAP PROOF *)
      (* ----- *)

      apply comp_spec_symm.
      fcf_skip_eq; kv_exist.
      simplify.

      (* get the right side 2 lines together to apply IH *)
      fcf_skip_eq; kv_exist.
      simplify.
      eapply comp_spec_eq_trans_r.
      Focus 2.

      instantiate (1 :=
                     (* Check ( *)
                         (res <-$ (k0 <-$ RndK;
                                       a0 <-$
                                         (oracleCompMap_inner
                                            (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                                        (pair_EqDec nat_EqDec eqDecState))
                                            (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
                                            (S calls, (k0, b)) xs) (list (Blist * Bvector eta))
                                         (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
                                       ret a0
                                      );
                              a2 <-$
                                 ([z, s']<-2 res;
                                  ([resList, state'']<-2 z; $ ret (a1 :: resList, state''))
                                    (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                                    rb_oracle s'); ret a2)).
       simplify. fcf_skip; kv_exist. simplify. fcf_skip_eq; kv_exist. 

      fcf_skip; kv_exist.
      fcf_ident_expand_l.

      instantiate (1 := (fun
              x0
               y : list (list (Bvector eta)) * (nat * KV) *
                   list (Blist * Bvector eta) => fst (fst x0) = fst (fst y))).
      assert (Hcalls : S calls <= i) by omega.
      pose proof (IHxs (S calls) i state Hcalls k b i_neq_0) as IHxs_inst.
      apply IHxs_inst. 

      simpl in H2. destruct b1. destruct p. simpl in *. subst. simplify.
      fcf_spec_ret.
      
    (* ------------------ *)

    (* this just seems to work out of the box after changes *)
    (* calls = i *)
    + Opaque Oi_oc''. Opaque Oi_oc'''.
      simplify.
      (* this doesn't seem to be true. there's an extra instantiate in Oi_oc'' *)
      (* fcf_irr_l. wfi. simplify. *)
      Transparent Oi_oc''. Transparent Oi_oc'''.
      simpl.
      assert (beq_nat calls i = true).
      { apply Nat.eqb_eq. auto. }
      rewrite H1.
      destruct (lt_dec calls i). omega. (* we have calls = i *)
      (* need a diff oracle.
in i != 0: in the latter, there's an extra instantiate in front and no kv updating, so everything's in sync
in i = 0: in the former, there's only k updating inside. in the latter, there's an extra instantiate in front (k,v). so the v's are not in sync *)
      (* separate theorem for i = 0? seems easier -- destruct -- on first call, k update, then afterward, easy induction? 
that would work but would that still apply to prove the top-level theorem??
       *)
      rewrite <- H0 in i_neq_0.
      destruct (beq_nat calls 0).
      { inversion i_neq_0. }

      (* i != 0 *)
      { Print GenUpdate_oc_instantiate.
        unfold Instantiate. simplify.
        (* now we have instantiate at the head of both, we can skip it, and the kv going into the loop  *)
        fcf_skip_eq; kv_exist.
        simplify. fcf_skip_eq; kv_exist. simplify.
        (* in fact only the k-update matters?? not true, we need the v's going in to be the same *) 
        (* loops are related *)
        fcf_skip; kv_exist.
        instantiate (1 := (fun x y => fst x = y)).
        (* both start with same v and x so postcondition holds *)
        { revert a a0 state. induction x as [ | x']; intros; simpl.
          - simplify. fcf_spec_ret.
          - unfold rb_oracle. simplify. fold rb_oracle. fcf_skip_eq.
            fcf_skip. simplify. fcf_spec_ret.
        }

        simpl in H3. destruct b1. inversion H3. subst.
        simplify.
        fcf_skip; kv_exist.
        instantiate (1 := (fun x y => fst x = fst y)).
        apply Oi_ocs_eq_calls_gt_i. omega.
        (* kv same AND calls > i! *)
        (* we're past RB and oracle, just PRFs here means oracles the same *)
        (* another induction w different states *)

        simplify. fcf_spec_ret. simpl in H6. destruct p. inversion H6. subst.
        simpl. reflexivity. }
Qed.

(* the oracleMap using Oi_prg (original computation) is equivalent to oracleCompMap using Oi_oc''' (the final one) 
for the second case of calls = i (leading to calls > i) *)
(* did this proof work? why did it break? *)
Lemma oracleMap_oracleCompMap_equiv_modified_calls_gt_i : forall l k v i state calls init,
   calls = i ->
   comp_spec
     (fun (x : list (list (Bvector eta)) * (nat * KV))
        (y : list (list (Bvector eta)) * (nat * KV) *
             list (Blist * Bvector eta)) => x = fst y)
     (compFold
        (pair_EqDec (list_EqDec (list_EqDec eqdbv))
           (pair_EqDec nat_EqDec eqDecState))
        (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
         [rs, s]<-2 acc;
         z <-$ Oi_prg (S i) s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
        (init, (calls, (k, v))) l)
     (z <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
         (calls, (k, v)) l) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state;
      [bits, nkv, state']<-3 z; ret (init ++ bits, nkv, state')).
Proof.
  (* modeled off Gi_normal_rb_eq_calls_eq_i *)
  Opaque Oi_prg. Opaque Oi_oc'''.
  destruct l as [ | x xs]; intros.
  (* why am I destructing l instead of inducting? *)

  - simplify. fcf_spec_ret. simpl. repeat (split; auto).
    rewrite app_nil_r; reflexivity.
  -
    simplify.
    eapply comp_spec_seq.
    (* avoid fcf_skip, it will subst calls = i, which i don't want to link. TODO why? *)

    apply (nil, (0, (oneVector eta, oneVector eta))).
    apply ((nil, (0, (oneVector eta, oneVector eta)), nil)).

    (* when calls = i, one is Gen_loop_rb and the other is Gen_loop_oc using the rb_oracle *)
    instantiate (1 := (fun c d => bitsVEq c d
                                  /\ fst (snd c) = S i /\ fst (snd (fst d)) = S i
                                  (* changed the postcondition; the keys now remain the same *)
                                  /\ fst (snd (snd c)) = fst (snd (snd (fst d))) )). (* TODO deleted =k, is that ok? *)
    (* 1 call: calls = i. why do i have to do the calls = i case again? shouldn't the other theorem cover it? *)
    { subst.
      Transparent Oi_prg. Transparent Oi_oc'''.
      unfold Oi_prg. unfold Oi_oc'''.
      simplify.
      (* casework on `i = 0`, `calls = i` and `calls > i` *)
      destruct (lt_dec i i). omega. 
      clear n.
      destruct (lt_dec i (S i)).
      Focus 2. omega. clear l.
      assert (idec : i = 0 \/ i <> 0) by omega.
      destruct idec as [ itrue | ifalse].
      SearchAbout (beq_nat _ _).
      apply beq_nat_true_iff in itrue.
      rewrite itrue.
      (* i = 0? shouldn't matter whether the v is updated an additional time in the latter *)
      (* TODO wait, i might need to pass the i=0 and i!=0 hypotheses down here? *)
      -
        fcf_skip; kv_exist.
        instantiate (1 := (fun x y => fst x = fst (fst y) /\ snd (snd x) = snd (snd (fst y))
                    /\ fst (snd x) = fst (snd (fst y)) = k)).
        (* can we weaken the postcondition? *)
        unfold GenUpdate_rb_intermediate. unfold GenUpdate_rb_intermediate_oc_noV.
        simplify.
        fcf_irr_l.
        fcf_skip_eq; kv_exist.
        (* TODO factor out *)
        {
          revert a k H0.
          induction x as [ | x']; intros; simplify.
          - fcf_spec_ret. f_equal. admit. (* TODO HOLE!! ADD HYP: x <> 0 *)
          - fcf_skip_eq.
        }
        (* hmm this saves the v, meaning the v gets updated... *)
        (* instantiate (1 := (fun x y => x = fst y)). *)
        (* unfold Gen_loop_rb. unfold Gen_loop_rb_intermediate. *)
        simplify. fcf_spec_ret.
        simpl in *. breakdown H2. simplify. fcf_spec_ret.
        destruct b. simpl in *. destruct k. simpl in *. subst. auto.
      -
        (* presumably now `i <> 0`? what assumptions hold here? *)
        assert (H_i_eq : beq_nat i i = true) by apply Nat.eqb_refl.
        rewrite H_i_eq.
        apply beq_nat_false_iff in ifalse.
        rewrite ifalse. simplify.
        fcf_skip; kv_exist.
        simplify.
        fcf_skip_eq; kv_exist.
        simplify. fcf_spec_ret. simpl. auto.
    }

    (* rest of calls -- induct on the new list *)
    { intros.
      (* don't do subst--there's an annoying link between calls and `i` that i don't want in my IH *)
      simplify. simpl in *. destruct p0. destruct p. destruct k1. simpl in *. destruct k0. simpl in H2. decompose [and] H2.
      rewrite H5. rewrite H3. rewrite H7. rewrite H9.
      clear H5 H3 H7 H9.
      clear H2 H1 H0.

      assert (n_eq : n = n0) by omega.
      rewrite <- H in H6.
      rewrite <- H in H4.
      rewrite n_eq.
      rename n0 into calls'.
      assert (H_calls : calls' > i) by omega.

      clear k v.
      rename b1 into k. rename b2 into v. rename l0 into rb_state.
      clear H6 n_eq H4 H. (* i cleared a lot of hypotheses here. might need them later? *)
      revert init k v rb_state i calls' H_calls l1.
      
      induction xs as [ | x' xs']; intros.

      (* xs = nil *)
      + simplify. fcf_spec_ret. 
      (* xs = x' :: xs', use IH *)
      + simplify.
        (*  "(list (Bvector eta) * KV * list (Blist * Bvector eta))%type" with
 "(list (Bvector eta) * KV)%type". *)
        fcf_skip; kv_exist.

        (* one call with calls > i (calls = S i) *)
        (* PRF oracle only *)
        clear calls. rename calls' into calls.

        instantiate (1 := (fun c d => c = fst d)).

        (* instantiate (1 := (fun c d => bitsVEq c d *)
        (*                               (* calls incremented by one *) *)
        (*                               /\ fst (snd c) = S calls *)
        (*                               /\ fst (snd (fst d)) = S calls *)
        (*                               (* KV equal *) *)
        (*                               /\ fst (snd (snd c)) = fst (snd (snd (fst d))))). *)
        {
          Transparent Oi_prg. Transparent Oi_oc'''.
          (* unfold Oi_prg. unfold Oi_oc'''. *)
          (* simplify. *)
          destruct (lt_dec calls (S i)). omega. (* calls > i, so ~(calls < S i) *)
          destruct (lt_dec calls i). omega.     (* calls > i, so ~(calls < i) *)
          assert (beq_nat calls 0 = false) as calls_neq_0.
          { apply Nat.eqb_neq. omega. }
          rewrite calls_neq_0. Opaque GenUpdate.
          assert (beq_nat calls i = false) as calls_neq_i.
          { apply Nat.eqb_neq. omega. }
          rewrite calls_neq_i.
          Transparent GenUpdate.
          simplify.
          fcf_spec_ret. 
          Opaque Oi_prg. Opaque Oi_oc'''.
        }

        simpl in H1. destruct b2. destruct p. simpl in *. inversion H1. subst.
        simplify.
        
        eapply comp_spec_eq_trans_r.
        destruct k0.
        eapply IHxs'.
        omega.
        
        (* now prove oracleCompMap_inner's eq *)
        { fcf_skip_eq.
          simplify. fcf_spec_ret.
          f_equal. f_equal.
          rewrite <- app_cons_eq.
          reflexivity.
        }
    } 
Qed.

(* TODO have to expand this with the fold and acc/++ *)
(* first case of the main proof (and the hardest case / main lemma): 
the original computation (oracleMap using Oi_prg) is equivalent to oracleCompMap Oi_oc'''
but only for the first case (calls <= i). is this induct, THEN destruct?
(TODO check the postcondition!) *)
Lemma oracleMap_oracleCompMap_equiv_modified : forall l k v i state calls init,
    calls <= i ->
    comp_spec
      (fun (x : list (list (Bvector eta)) * (nat * KV))
           (y : list (list (Bvector eta)) * (nat * KV) *
                list (Blist * Bvector eta)) => x = fst y)
      (compFold
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                     (pair_EqDec nat_EqDec eqDecState))
         (fun (acc : list (list (Bvector eta)) * (nat * KV)) (d : nat) =>
            [rs, s]<-2 acc;
          z <-$ Oi_prg (S i) s d; [r, s0]<-2 z; ret (rs ++ r :: nil, s0))
         (init, (calls, (k,v))) l)
      ([acc', state'] <-$2 ((oracleCompMap_inner
                               (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                           (pair_EqDec nat_EqDec eqDecState))
                               (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
                               (calls, (k, v)) l) (list (Blist * Bvector eta))
                                                  (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle state);
       [bits, nkv] <-2 acc';
       ret (init ++ bits, nkv, state')).
Proof.
  (* modeled off Gi_normal_rb_eq_compspec *)
  (* induct, then destruct *)
  induction l as [ | x xs]; intros.
  - simplify. fcf_spec_ret. simpl. rewrite app_nil_r. repeat (split; auto).
  - assert (H_ilen : calls < i \/ calls = i) by omega.
    destruct H_ilen.
    clear H.

    (* calls < i *)
    Opaque Oi_prg. Opaque Oi_oc'''.
    simplify.
    fcf_skip; kv_exist.
    (* case: call on first element of list *)
    (* strengthen postcondition so we can prove calls < i -> S calls <= i to apply IHxs *)
    (* also strengthen it again because if calls < i then the keys must still be the same *)
    instantiate (1 := (fun c d => bitsVEq c d
                                  (* calls incremented by 1 *)
                                  /\ fst (snd c) = S calls /\ fst (snd (fst d)) = S calls
                                  (* output keys are the input keys *)
                                  /\ fst (snd (snd c)) = k
                                  /\ fst (snd (snd (fst d))) = k)).
    (* includes calls *)
    (* one call with linked keys TODO *)
    {
      Transparent Oi_prg. Transparent Oi_oc'''.
      simpl.
      destruct (lt_dec calls i).
      Focus 2. omega.         (* contradiction *)
      clear l.                (* calls < i *)
      assert (H_calls_lt : calls < S i) by omega.
      destruct (lt_dec calls (S i)).
      Focus 2. omega. 
      fcf_skip; kv_exist.   (* GenUpdate_rb_intermediate(_oc) *)
      (* postcondition: output keys are unchanged from input *)
      instantiate (1 := (fun x y => x = fst y /\ fst (snd x) = fst (snd (fst y)) = k)).
      unfold GenUpdate_rb_intermediate.
      simplify.
      fcf_skip_eq; kv_exist.
      simplify.
      fcf_skip_eq; kv_exist.
      simplify.
      fcf_spec_ret.

      simpl in *. inversion H2. destruct b0. simpl in *. destruct b. destruct p. simpl in *. destruct k0. simpl in *.
      inversion H4. inversion H3. subst. simplify. fcf_spec_ret. simpl. auto.
      } 


    (* use IH *)
    { simpl in H2. destruct b0. destruct b. destruct p. destruct p. destruct k0. simpl in *.
      breakdown H2. 
      simplify.

      eapply comp_spec_eq_trans_r.
      eapply IHxs; omega. 
      instantiate (1 := l).
      (* now prove oracleCompMap_inner's eq *)
      { fcf_skip_eq; kv_exist.
        simplify.
        fcf_spec_ret. f_equal. f_equal. rewrite <- app_assoc. f_equal.
      }
    } 
    
    (* calls = i *)
    + clear IHxs.
      clear H.
      apply oracleMap_oracleCompMap_equiv_modified_calls_gt_i; omega.
      (* apply Gi_normal_rb_eq_calls_eq_i; omega. *) 
Qed.

Transparent Oi_prg.
Lemma Gi_normal_rb_eq : forall (i : nat),
    Pr[Gi_prg (S i)] == Pr[Gi_rb i].
Proof.
  intros.
  unfold Gi_prg.
  unfold Gi_rb.
  unfold PRF_Adversary.
  unfold oracleCompMap_outer.
  fcf_to_prhl_eq.
  simplify.

  (* apply first theorem *)
  rewrite_r.
  (* replace Oi_oc' with Oi_oc'' *)
  instantiate
    (1 :=
         (a <-$ Instantiate;
      a0 <-$ ret (a, nil);
      a1 <-$
      ([z, s']<-2 a0;
       ([k, v]<-2 z;
        z0 <--$
        oracleCompMap_inner
          (pair_EqDec (list_EqDec (list_EqDec eqdbv))
             (pair_EqDec nat_EqDec eqDecState))
          (list_EqDec (list_EqDec eqdbv)) (Oi_oc'' i) 
          (0, (k, v)) maxCallsAndBlocks; [bits, _]<-2 z0; $ ret bits)
         (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
         rb_oracle s');
      z <-$ ([z, s']<-2 a1; x <-$ A z; ret (x, s')); [b, _]<-2 z; ret b)). 
  { fcf_skip_eq. simplify. fcf_skip. apply oracleCompMap_rb_instantiate_inner.
    simplify. simpl in *. destruct p. inversion H1. subst. fcf_skip_eq.
    simplify. fcf_reflexivity. }

  (* casework on i, apply second or third theorems *)
  flip. 
  assert (i_cases: beq_nat i 0 = true \/ beq_nat i 0 = false).
  { destruct i; auto. }
  destruct i_cases.

  (* i = 0 *)
  - rewrite_r.                  (* replace Oi_oc'' with Oi_oc''' *)
    instantiate
      (1 :=
         ([k,v] <-$2 Instantiate;
          k <-$ RndK;
          a0 <-$ ret ((k,v), nil);
          a1 <-$
             ([z, s']<-2 a0;
              ([k, v]<-2 z;
               z0 <--$
                  oracleCompMap_inner
                  (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                              (pair_EqDec nat_EqDec eqDecState))
                  (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) (* note triple prime *)
                  (0, (k, v)) maxCallsAndBlocks; [bits, _]<-2 z0; $ ret bits)
                (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                rb_oracle s');
          z <-$ ([z, s']<-2 a1; x <-$ A z; ret (x, s')); [b, _]<-2 z; ret b)).
    {
    (* need to isolate first 4 lines of each, rewrite with each, prove each equiv, then rewrite with oracleCompMap_rb_instantiate_outer_i_eq_0 *)
      flip. rewrite_r.
      instantiate
        (1 :=
           (top <-$
                ([k,v] <-$2 Instantiate;
                  a <-$ (oracleCompMap_inner
                         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                     (pair_EqDec nat_EqDec eqDecState))
                         (list_EqDec (list_EqDec eqdbv)) (Oi_oc'' i) 
                         (0, (k, v)) maxCallsAndBlocks) 
                       (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                       rb_oracle nil;
                 ret a);
            z <-$ ([bnkv, s']<-2 top; [bits, _] <-2 bnkv; x <-$ A bits; ret (x, s')); [b, _]<-2 z; ret b)).
      { prog_equiv. }
      rewrite_r.
      instantiate
        (1 :=
           (top <-$
                ([k,v] <-$2 Instantiate;
                 k <-$ RndK;
                 a <-$ (oracleCompMap_inner
                         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                     (pair_EqDec nat_EqDec eqDecState))
                         (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
                         (0, (k, v)) maxCallsAndBlocks
                       (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                       rb_oracle nil);
                 ret a);
                z <-$ ([bnkv, s']<-2 top; [bits, _] <-2 bnkv; x <-$ A bits; ret (x, s')); [b, _]<-2 z; ret b)).
      { prog_equiv. }
      fcf_skip. flip. apply oracleCompMap_rb_instantiate_outer_i_eq_0. auto.

      simpl in H2. destruct b0. destruct a. simpl in *. destruct p. simpl in *. subst.
      simplify. fcf_skip_eq. simplify. fcf_spec_ret.

      simpl in H2. destruct p. destruct l1. simpl in *. rewrite H2.
      simplify. fcf_skip_eq. simplify. fcf_spec_ret.

      simpl in H2. rewrite H2.
      simplify. fcf_skip_eq. simplify. fcf_spec_ret.
    } 
    flip.
    unfold Instantiate. simplify.
    fcf_irr_r. unfold RndK. fcf_well_formed.
    simplify.
    rewrite_r.
    instantiate
      (1 :=
         (k0 <-$ RndK;
          a <-$ RndV;
          z1 <-$ ret (b, a);
          [_, v]<-2 z1;
          a0 <-$ ret (k0, v, nil);
          a1 <-$
             ([z, s']<-2 a0;
              ([k1, v0]<-2 z;
               z0 <--$
                  oracleCompMap_inner
                  (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                              (pair_EqDec nat_EqDec eqDecState))
                  (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
                  (0, (k1, v0)) maxCallsAndBlocks; [bits, _]<-2 z0; $ ret bits)
                (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                rb_oracle s');
          z <-$ ([z, s']<-2 a1; x <-$ A z; ret (x, s')); [b0, _]<-2 z; ret b0)).
    { fcf_swap fcf_right. prog_equiv. }
    flip.
    prog_equiv.
    (* factor out lemma and apply it to both cases *)
    fcf_skip. instantiate (1 := (fun x y => x = fst y)).
    (* they have the same k and v, former is S i, latter is i without updates in RB, so i hope this works! *)
    unfold oracleMap.
    pose proof oracleMap_oracleCompMap_equiv_modified.
    eapply comp_spec_eq_trans_r. apply H1. omega. 
    instantiate (1 := nil). fcf_ident_expand_r. fcf_skip_eq; kv_exist.
    simpl. fcf_spec_ret.

    simpl in H3. destruct b0. repeat destruct p. simpl in *. inversion H3. subst.
    fcf_ident_expand_l. simplify. prog_equiv. fcf_spec_ret.
  (* looks like the i=0 case is fully proved *)

  (* i != 0 *)
  - rewrite_r.
    instantiate
      (1 :=
         ([k,v] <-$2 Instantiate;
          (* [k,v] <-$2 Instantiate; *)
          k <-$ RndK;
          a0 <-$ ret ((k,v), nil);
          a1 <-$
             ([z, s']<-2 a0;
              ([k, v]<-2 z;
               z0 <--$
                  oracleCompMap_inner
                  (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                              (pair_EqDec nat_EqDec eqDecState))
                  (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) (* note triple prime *)
                  (0, (k, v)) maxCallsAndBlocks; [bits, _]<-2 z0; $ ret bits)
                (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                rb_oracle s');
          z <-$ ([z, s']<-2 a1; x <-$ A z; ret (x, s')); [b, _]<-2 z; ret b)).
    {
    (* need to isolate first 4 lines of each, rewrite with each, prove each equiv, then rewrite with oracleCompMap_rb_instantiate_outer_i_eq_0 *)
      flip. rewrite_r.
      instantiate
        (1 :=
           (top <-$
                ([k,v] <-$2 Instantiate;
                  a <-$ (oracleCompMap_inner
                         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                     (pair_EqDec nat_EqDec eqDecState))
                         (list_EqDec (list_EqDec eqdbv)) (Oi_oc'' i) 
                         (0, (k, v)) maxCallsAndBlocks) 
                       (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                       rb_oracle nil;
                 ret a);
            z <-$ ([bnkv, s']<-2 top; [bits, _] <-2 bnkv; x <-$ A bits; ret (x, s')); [b, _]<-2 z; ret b)).
      { prog_equiv. }
      rewrite_r.
      instantiate
        (1 :=
           (top <-$
                ([k,v] <-$2 Instantiate;
                 (* [k,v] <-$2 Instantiate; *)
                 k <-$ RndK;
                 a <-$ (oracleCompMap_inner
                         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                     (pair_EqDec nat_EqDec eqDecState))
                         (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
                         (0, (k, v)) maxCallsAndBlocks
                       (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                       rb_oracle nil);
                 ret a);
                z <-$ ([bnkv, s']<-2 top; [bits, _] <-2 bnkv; x <-$ A bits; ret (x, s')); [b, _]<-2 z; ret b)).
      { prog_equiv. }

     fcf_skip. flip. 

      apply oracleCompMap_rb_instantiate_outer_i_neq_0.
      omega. auto.

      simpl in H2. destruct b0. destruct a. simpl in *. destruct p. simpl in *. subst.
      prog_equiv. fcf_spec_ret.

      simpl in H2. destruct p. destruct l1. simpl in *. rewrite H2.
      prog_equiv. fcf_spec_ret.

      simpl in H2. rewrite H2.
      prog_equiv. fcf_spec_ret.
    } 
    flip.
    unfold Instantiate. simplify.
    fcf_irr_r. unfold RndK. fcf_well_formed.
    simplify.

    rewrite_r.
    instantiate (1 := 
                   (k0 <-$ RndK;
                    a <-$ RndV;
                    z1 <-$ ret (b, a);
                    [_, v]<-2 z1;
                    a0 <-$ ret (k0, v, nil);
                    a1 <-$
                       ([z, s']<-2 a0;
                        ([k1, v0]<-2 z;
                         z0 <--$
                            oracleCompMap_inner
                            (pair_EqDec (list_EqDec (list_EqDec eqdbv))
                                        (pair_EqDec nat_EqDec eqDecState))
                            (list_EqDec (list_EqDec eqdbv)) (Oi_oc''' i) 
                            (0, (k1, v0)) maxCallsAndBlocks; [bits, _]<-2 z0; $ ret bits)
                          (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
                          rb_oracle s');
                    z <-$ ([z, s']<-2 a1; x <-$ A z; ret (x, s')); [b0, _]<-2 z; ret b0) ).
    { fcf_swap fcf_right. prog_equiv. }

    fcf_skip_eq. simplify.
    fcf_skip_eq. simplify.
    apply comp_spec_symm.

    (* factor out lemma and apply it to both cases *)
    fcf_skip. 
    (* instantiate (1 := (fun x y => x = fst y)). *)
    unfold oracleMap.
    pose proof oracleMap_oracleCompMap_equiv_modified as om_ocm_equiv.
    eapply comp_spec_eq_trans_r. apply om_ocm_equiv. omega. 
    instantiate (1 := nil). fcf_ident_expand_r. fcf_skip_eq; kv_exist.
    simpl. fcf_spec_ret.

    simpl in H3. destruct b0.
    simpl in *. destruct p. destruct p. inversion H3. subst.
    simplify.
    fcf_ident_expand_l. simplify. prog_equiv. fcf_reflexivity.
Qed.

(* attempting proof for when every RB uses the last v: (meaning the adversary doesn't request 0 blocks?)
BUT need to make the change at the top level, 
merge it into Gi_normal_prf, (just check first)
and add 'list <> 0' assumptions everywhere
and confirm it doesn't break ANYTHING referring to Gi_prg
  looks like Pr_collisions could be fine too?
STEP BACK: is this theorem actually true? intuition says yes bc the structures are the same now

WANT TO PROVE

eq
([k,v] <-2 Instantiate;
oracleMap (Oi_prg (S i)) (0, (k,v)) l)
([k,v] <-2 Instantiate;
oracleCompMap_inner (Oi_oc' i) (0, (k,v)) l)

----

calls < i:

eq
([k,v] <-2 Instantiate;
v' <-$ Rnd;
[bits,v''] <- Gen_loop_last v' n;
oracleMap (Oi_prg (S i)) (1, (k,v'')) ns)

([k,v] <-2 Instantiate;
v' <-$ Rnd;
[bits,v''] <- Gen_loop_last v' n;
oracleCompMap_inner (Oi_oc' i) (1, (k,v'')) ns)

what structures do I use? remember, CAN'T UPDATE K AT ALL. not even on both sides ( * why?)
anyway, should be ok for calls < i, since same structure
how to do induction like last time? push instantiate in? TODO?
the calls=i case looks good but can i even push the Instantiate in? I didn't manage to pull one out either? so now I'm just confused? is the below possible? I definitely need to push the k in for the later k update (and the k *can* be pushed in). and apparently I don't need to push the v in?

try this form:

WANT TO PROVE

eq
(v <- RndV;
k <- RndK;
oracleMap (Oi_prg (S i)) (0, (k,v)) l)
(v <- RndV;
k <- RndK;
oracleCompMap_inner (Oi_oc' i) (0, (k,v)) l)

so we skip. forall v,

eq
(k <- RndK;
oracleMap (Oi_prg (S i)) (0, (k,v)) l)
(k <- RndK;
oracleCompMap_inner (Oi_oc' i) (0, (k,v)) l)

and, after reverting, we induct on l. now we are GIVEN

IH: forall v, (and forall calls, k, v, i)
eq
(k <- RndK;
oracleMap (Oi_prg (S i)) (calls, (k,v)) xs)
(k <- RndK;
oracleCompMap_inner (Oi_oc' i) (calls, (k,v)) xs)

and WANT TO PROVE:

eq
(k <- RndK;
oracleMap (Oi_prg (S i)) (0, (k,v)) x::xs)
(k <- RndK;
oracleCompMap_inner (Oi_oc' i) (0, (k,v)) x::xs)

(-this isn't quite right--it's actually calls < i \/ calls = i, not calls = 0. but the overall induct-then-destruct structure is okay)
(-did i deal with the calls=0 special case?
i think it's ok since they both do the same thing? but what if i=0 or something)
(-when i do the proof, need to verify these theorem statements are correct)

expanding the call:
( * assuming in the beginning we do GenUpdate_rb on both left and right? if i=0)

eq
(k <-$ Rnd;
v' <- Rnd;
[bits,v''] <- Gen_loop_last v' n;
oracleMap (Oi_prg (S i)) (1, (k,v'')) xs) 

(k <-$ Rnd;
v' <- Rnd;
[bits,v''] <- Gen_loop_last v' n;
oracleCompMap_inner (Oi_oc' i) (1, (k,v'')) xs)

(this expansion assumes calls < i)
the k is irrelevant so we can swap it to before the last line, and skip the v and bits first
*** being able to prove k irrelevant and swap it to the back seems like a major lemma
*** if k is used anywhere in between, then we need to skip the k sample, otherwise there's no variable
(however, it doesn't look like GenUpdate_rb uses the k at all)
(BTW the intermediate postcondition may be different, but it'll probably be eq)

eq
(k <-$ Rnd;
oracleMap (Oi_prg (S i)) (1, (k,v'')) xs)

(k <-$ Rnd;
oracleCompMap_inner (Oi_oc' i) (1, (k,v'')) xs)

does this match the IH? yes, actually.... because it's forall v now?
so, this could work?

----

calls = i: 
( *ns here should be xs?)

eq
(k <-$ Rnd;
v' <-$ Rnd;
[bits,v''] <- Gen_loop_last v' n; <--- @@@ this is the problem: the real RB does not currently update v, but we'll change it to do so
oracleMap (Oi_prg (S i)) (S i, (k,v'')) ns)

(k <-$ Rnd;
v' <-$ Rnd;
<**>
[bits,v''] <- Gen_loop_last v' n;
k' <-$ Rnd;
oracleCompMap_inner (Oi_oc' i) (S i, (k',v'')) ns)

<**> how come we can ignore the v from instantiate? did I forget to type this line?
if every RB uses the last v, then it doesn't matter if v is re-sampled, since we'll just sample it again (-in gen_loop_last?) 
(as long as we never request 0 blocks)?
(-gen_loop_last doesn't use the input v', and the v'' are resampled uniformly as long as n>0)

there's just an extra k, so manipulate the rightmost. 
the last k re-sampling can be moved to before the loop

eq
(k <- Rnd;
v' <-$ Rnd;
[bits,v''] <- Gen_loop_last v' n;
oracleMap (Oi_prg (S i)) (S i, (k,v'')) ns)

(k <- Rnd;
k' <-$ Rnd;
v' <-$ Rnd;
[bits,v''] <- Gen_loop_last v' n;
oracleCompMap_inner (Oi_oc' i) (S i, (k',v'')) ns)

--> do fcf_irr_r *on the first k on the right (from the instantiate) 
+ switch *the resulting first 2 lines on the left

eq
(k <- Rnd;
v' <-$ Rnd;
[bits,v''] <- Gen_loop_last v' n;
oracleMap (Oi_prg (S i)) (S i, (k,v'')) ns)

(k' <-$ Rnd;
v' <-$ Rnd;
[bits,v''] <- Gen_loop_last v' n;
oracleCompMap_inner (Oi_oc' i) (S i, (k',v'')) ns)

--> skip

eq
(v' <-$ Rnd;
[bits,v''] <- Gen_loop_last v' n;
oracleMap (Oi_prg (S i)) (S i, (k,v'')) ns)

(v' <-$ Rnd;
[bits,v''] <- Gen_loop_last v' n;
oracleCompMap_inner (Oi_oc' i) (S i, (k',v'')) ns)

then both are the same? so we can prove k,v,bits are the same?
in fact we don't need the v from instantiate, just the k
TODO how do i deal with noV then? apparently it doesn't matter?
that only matters if
* if what?
* do we use the IH here? why or why not? no IH, only for calls < i, different IH for calls > i

maybe I mistyped the statement and the end result actually has an extra v-sampling, but it doesn't matter
(see email)
----

calls > i:

again unsure if both instantiates will still be here? 
just need that the inputted k v are the same and the outputted bits are the same 

eq
(k <-$ RndK;
v' <-$ f k v;
[bits,v''] <- Gen_loop_PRF k v n;
k' <-$ f k (v''||00);
oracleMap (Oi_prg (S i)) (?, (k',v'')) ns)

(k <-$ RndK;
v' <-$ f k v;
[bits,v''] <- Gen_loop_PRF k v n;
k' <-$ f k (v''||00);
oracleCompMap_inner (Oi_oc' i) (?, (k',v'')) ns) *)

  
(* does not hold for i = 0:
Gi_prg 0: PRF PRF PRF...
Gi_prg 1: RB PRF PRF...
Gi_rb 0 : RB PRF PRF... 
(call number 0 uses the RB oracle) -- equivalence, no replacing happening here *)
(* might have misnumbered something here? *)
(* using random bits as the oracle for the ith call = the (i+1)th hybrid *)
(* proof very similar to Gi_normal_prf_eq 
used in Gi_rf_rb_close to move from Gi_prg (S i) to Gi_rb i *)

  (* what would it mean to put the former in terms of an oracle interaction? wouldn't that just be this theorem? *)
  (* TODO email adam about PRF adversary *)
(* this proof doesn't quite work *)
  (* maybe prove that i can "cut out" the k and v, and re-instantiate it on the `i`th call?
     (or just re-instantiate it.)
   then the types would change?
   also, would it just be shifting the problem around?
   would the induction still work?? we wouldn't want Instantiate in the hypothesis

  can I also prove, in the latter, that the k,v update can be moved OUT when we're using RB?
or at least moved out together into an Instantiate in the beginning of calls=i.
can i further prove that it can be moved out altogether, into before oracleCompMap_inner?
then i could skip the first leftmost Instantiate
the problem is again, what do i do with inducting while Instantiate is in the statement??

proof outline:

left:
Instantiate, oracleCompMap (calls = i: Instantiate; generate bits)

right:
Instantiate, Instantiate, oracleCompMap (calls = i: generate bits)

-> fcf_skip first Instantiate

left:
kv -> oracleCompMap (calls = i: Instantiate; generate bits) l

right:
kv -> Instantiate, oracleCompMap (calls = i: generate bits) l

induct on l

->
IH:
(left:
forall kv, oracleCompMap (calls = i: Instantiate; generate bits) xs

right:
forall kv, Instantiate; oracleCompMap (calls = i: generate bits) xs)

- show
(left:
forall kv, Oi_oc x; oracleCompMap (calls = i: Instantiate; generate bits) xs

right:
forall kv, Instantiate; Oi_oc x; oracleCompMap (calls = i: generate bits) xs)

- rewrite:
what's the condition on calls?
either calls < i or calls = i

- first: calls < i

(left:
forall kv, Oi_oc x; oracleCompMap (calls = i: Instantiate; generate bits) xs

right:
if calls < i, then Instantiate is irrelevant (we already have a kv), so we can move it after
forall kv, Oi_oc x; Instantiate; oracleCompMap (calls = i: generate bits) xs)

then fcf_skip the first, which is equal (calls < i)

new state:
(left:
forall kv, oracleCompMap (calls = i: Instantiate; generate bits) xs

right:
if calls < i, then Instantiate is irrelevant (we already have a kv), so we can move it after
forall kv, Instantiate; oracleCompMap (calls = i: generate bits) xs)

apply the induction hypothesis! yay!

- second: calls = i

(left:
forall kv, Oi_oc [calls = i: Instantiate; generate bits] x; oracleCompMap xs

right:
forall kv, Instantiate; Oi_oc [calls = i: generate bits] x; oracleCompMap xs)

now we can pull out the Instantiate on the left:

(left:
forall kv, Instantiate; Oi_oc [calls = i: generate bits] x; oracleCompMap xs

right:
forall kv, Instantiate; Oi_oc [calls = i: generate bits] x; oracleCompMap xs)

and apply fcf_reflexivity!

---

and if this works, we can work with 

left: 
Instantiate, oracleMap

right:
Instantiate, Instantiate, oracleCompMap (calls = i: generate bits)

(irr_r)->

left: 
Instantiate, oracleMap

right:
Instantiate, oracleCompMap (calls = i: generate bits)

->

left: 
kv -> oracleMap

right:
kv -> oracleCompMap (calls = i: generate bits)

and inside the inner computation, we should be able to skip the two loops and end up with unchanged k and their two v's will be the same!

----

for i = 0, top-level theorem:

Instantiate, oracleMap
Instantiate, RndK, oracleCompMap (calls=0: generate)

->

RndK, RndV, oracleMap
RndK, RndV, RndK, oracleCompMap (calls=0: generate)

-> (irr_r)

RndK, RndV, oracleMap
RndV, RndK, oracleCompMap (calls=0: generate)

-> (swap)

RndK, RndV, oracleMap
RndK, RndV, oracleCompMap (calls=0: generate)

-> proceed as above (split out lemma??)

see Lemma i_eq_0_k_mask_test above for proof that this works

----

i also forgot about the whole "v is not updated twice on the first call" :-/

can i prove things for updating v only in GenUpdate_rb_int.?
note i only have to relate them on calls=i   *)

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

  - fcf_well_formed. (* TODO hole: prove entire oraclecompmap is well_formed (how?) *)
    SearchAbout well_formed_oc.
    (* unfold well_formed_oc. *)
    admit.
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
  fcf_skip_eq; kv_exist.
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

Close Scope nat.
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

Opaque hasDups.
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

(* DONE *)
(* remove adversary (easy) *)
Lemma Gi_rb_bad_eq_1 : forall (i : nat),
    Pr [x <-$ Gi_rb_bad i; ret snd x] == Pr [Gi_rb_bad_no_adv i].
Proof.
  intros.
  fcf_to_prhl_eq.
  unfold Gi_rb_bad.
  unfold Gi_rb_bad_no_adv.
  prog_equiv.
  fcf_irr_l.
  prog_equiv.
  fcf_spec_ret.
Qed.

(*---------- Gi_rb_bad_eq_2 (splitting out `i`th call) *)
Open Scope nat.

Lemma split_out_oracle_call : forall (nCalls : nat) (k v : Bvector eta) (calls i : nat) (init : list (Blist * Bvector eta)),
   calls <= i ->
   nCalls > 0 ->
   comp_spec eq
     (a <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (calls, (k, v)) (replicate nCalls blocksPerCall)) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle init;
      a0 <-$
      ([z, s']<-2 a;
       ([bits, _]<-2 z; $ ret bits) (list (Blist * Bvector eta))
         (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle s');
      z <-$ ([z, s']<-2 a0; x <-$ ret z; ret (x, s'));
      [_, state]<-2 z; ret hasInputDups state)
     (z <-$
      (GenUpdate_oc (k, v) blocksPerCall) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle init;
      [_, state]<-2 z; ret hasInputDups state).
Proof.
  destruct nCalls as [ | nCalls']; intros; rename H into calls_leq_i.
  (* nCalls > 0 *)
  - omega.
  (* first call *)
  - Opaque Oi_oc'. Opaque GenUpdate_oc. simplify.
    assert (Hcalls : calls < i \/ calls = i) by omega.
    destruct Hcalls.
    (* either calls < i or calls = i *)
    (* if calls < i... then the one call doesn't matter, and at some point calls = i, which reduces to the second case *)
    (* need some kind of induction here? maybe *another* calls < i \/ calls = i? or just induct as-is? *)

    (* if calls = i: then Oi_oc' i simplifies to GenUpdate_oc, and the states should be the same after. 
       then need to deal with rest of calls: now calls > i. induct, and show that given the same starting rb_oracle state (right side empty), then for a subsequent call, the state doesn't change, so hasInputDups doesn't change ?
 *)
    
    admit.

(* another induction? *)

Admitted.

Lemma test_same_goal : forall (k v : Bvector eta) (i : nat),
   comp_spec eq
     (a <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (0%nat, (k, v)) (replicate numCalls blocksPerCall))
        (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
        rb_oracle nil;
      a0 <-$
      ([z, s']<-2 a;
       ([bits, _]<-2 z; $ ret bits) (list (Blist * Bvector eta))
         (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle s');
      z <-$ ([z, s']<-2 a0; x <-$ ret z; ret (x, s'));
      [_, state]<-2 z; ret hasInputDups state)
     (z <-$
      (GenUpdate_oc (k, v) blocksPerCall) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle (@nil (Blist * Bvector eta));
      [_, state]<-2 z; ret hasInputDups state).
Proof.
Admitted.

Close Scope nat.

Lemma eqt1 : forall k v,
    comp_spec eq
              (z <-$
                 (GenUpdate_oc (k, v) blocksPerCall) (list (Blist * Bvector eta))
                 (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle nil;
               [_, state]<-2 z; ret hasInputDups state)
     (z <-$
      (GenUpdate_oc (k, v) blocksPerCall) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle nil;
      [_, state]<-2 z; ret hasInputDups state).
Proof.
  intros.
  assert (H :    comp_spec eq
     (z <-$
      (GenUpdate_oc (k, v) blocksPerCall) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle nil;
      [_, state]<-2 z; ret hasInputDups state)
     (z <-$
      (GenUpdate_oc (k, v) blocksPerCall) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle nil;
      [_, state]<-2 z; ret hasInputDups state)). { admit. }
  apply H.                                                 
Qed.

Lemma eqt2 : forall k v i,
   comp_spec eq
     (a <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (0%nat, (k, v)) (replicate numCalls blocksPerCall))
        (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
        rb_oracle nil;
      a0 <-$
      ([z, s']<-2 a;
       ([bits, _]<-2 z; $ ret bits) (list (Blist * Bvector eta))
         (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle s');
      z <-$ ([z, s']<-2 a0; x <-$ ret z; ret (x, s'));
      [_, state]<-2 z; ret hasInputDups state)
     (a <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (0%nat, (k, v)) (replicate numCalls blocksPerCall))
        (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
        rb_oracle nil;
      a0 <-$
      ([z, s']<-2 a;
       ([bits, _]<-2 z; $ ret bits) (list (Blist * Bvector eta))
         (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle s');
      z <-$ ([z, s']<-2 a0; x <-$ ret z; ret (x, s'));
      [_, state]<-2 z; ret hasInputDups state).
Proof.
  intros.
  assert (H :    comp_spec eq
     (a <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (0%nat, (k, v)) (replicate numCalls blocksPerCall))
        (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
        rb_oracle nil;
      a0 <-$
      ([z, s']<-2 a;
       ([bits, _]<-2 z; $ ret bits) (list (Blist * Bvector eta))
         (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle s');
      z <-$ ([z, s']<-2 a0; x <-$ ret z; ret (x, s'));
      [_, state]<-2 z; ret hasInputDups state)
     (a <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (0%nat, (k, v)) (replicate numCalls blocksPerCall))
        (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
        rb_oracle nil;
      a0 <-$
      ([z, s']<-2 a;
       ([bits, _]<-2 z; $ ret bits) (list (Blist * Bvector eta))
         (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle s');
      z <-$ ([z, s']<-2 a0; x <-$ ret z; ret (x, s'));
      [_, state]<-2 z; ret hasInputDups state)). { admit. }
  apply H.
Qed.                                                 

(* Check eqdbv. *)
(* Definition etn := 1%nat. *)
(* Variable eqdbvn : EqDec (Bvector etn). *)

Lemma eqt3 : forall k v i,
   comp_spec eq
     (a <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (0%nat, (k, v)) (replicate numCalls blocksPerCall))
        (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
        rb_oracle nil;
      a0 <-$
      ([z, s']<-2 a;
       ([bits, _]<-2 z; $ ret bits) (list (Blist * Bvector eta))
         (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle s');
      z <-$ ([z, s']<-2 a0; x <-$ ret z; ret (x, s'));
      [_, state]<-2 z; ret hasInputDups state)
     (z <-$
      (GenUpdate_oc (k, v) blocksPerCall) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle nil;
      [_, state]<-2 z; ret hasInputDups state).
Proof.
intros.
assert (H :    comp_spec eq
     (a <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (0%nat, (k, v)) (replicate numCalls blocksPerCall))
        (list (Blist * Bvector eta)) (list_EqDec (pair_EqDec eqdbl eqdbv))
        rb_oracle nil;
      a0 <-$
      ([z, s']<-2 a;
       ([bits, _]<-2 z; $ ret bits) (list (Blist * Bvector eta))
         (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle s');
      z <-$ ([z, s']<-2 a0; x <-$ ret z; ret (x, s'));
      [_, state]<-2 z; ret hasInputDups state)
     (z <-$
      (GenUpdate_oc (k, v) blocksPerCall) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle nil;
      [_, state]<-2 z; ret hasInputDups state)).
{ admit. }
apply H.
Qed.

(* only the ith call with GenUpdate_oc (does it depend on what i is? casework on whether 0) ** hard *)
Lemma Gi_rb_bad_eq_2 : forall (i : nat),
    Pr [Gi_rb_bad_no_adv i] == Pr [Gi_rb_bad_only_oracle].
Proof.
(* left hand side: RB' RB RB RO PRF PRF...
   right hand side:          RO            *)
  (* where RO denotes "random bits oracle" (it's only used in the `i`th call! *)
  (* Set Printing Implicit. *)
  intros.
  fcf_to_prhl_eq.
  unfold Gi_rb_bad_no_adv.
  unfold Gi_rb_bad_only_oracle.
  unfold callMapWith.           (* what is this? get rid of adversary *)
  unfold oracleCompMap_outer.
  (* Opaque GenUpdate_oc. *)
  (* Opaque oracleCompMap_inner. *)
  simplify.
  fcf_skip_eq.
  simplify.
  rename b into k. rename b0 into v.
  unfold maxCallsAndBlocks.

  apply eqt3.
(* Print Implicit split_out_oracle_call. *)

  assert (0 <= i)%nat by omega.
  pose proof (@split_out_oracle_call numCalls k v 0%nat i nil H H_numCalls).

  (* Set Printing Implicit. *)
  (* eapply H0. *)

  (* eapply split_out_oracle_call. *)

  (* pose proof (test_same_goal k v i). *)
  (* apply H.   *)

  assert (test_same_goal' : 
               comp_spec eq
     (a <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbvn))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbvn)) (Oi_oc' i) 
         (0%nat, (k, v)) (replicate numCalls blocksPerCall))
        (list (Blist * Bvector etn)) (list_EqDec (pair_EqDec eqdbl eqdbvn))
        rb_oracle nil;
      a0 <-$
      ([z, s']<-2 a;
       ([bits, _]<-2 z; $ ret bits) (list (Blist * Bvector etn))
         (list_EqDec (pair_EqDec eqdbl eqdbvn)) rb_oracle s');
      z <-$ ([z, s']<-2 a0; x <-$ ret z; ret (x, s'));
      [_, state]<-2 z; ret hasInputDups state)
     (z <-$
      (GenUpdate_oc (k, v) blocksPerCall) (list (Blist * Bvector etn))
        (list_EqDec (pair_EqDec eqdbl eqdbvn)) rb_oracle nil;
      [_, state]<-2 z; ret hasInputDups state) 
).
  { admit. }
  assert (test_same_goal2 : 
   @comp_spec bool bool bool_EqDec bool_EqDec (@eq bool)
     (a <-$
      (@oracleCompMap_inner nat (list (Bvector etn)) Blist 
         (Bvector etn)
         (@pair_EqDec (list (list (Bvector etn))) (nat * KV)
            (@list_EqDec (list (Bvector etn))
               (@list_EqDec (Bvector etn) eqdbvn))
            (@pair_EqDec nat KV nat_EqDec eqDecState))
         (@list_EqDec (list (Bvector etn)) (@list_EqDec (Bvector etn) eqdbvn))
         (Oi_oc' i) (0%nat, (k, v)) (@replicate nat numCalls blocksPerCall))
        (list (Blist * Bvector etn))
        (@list_EqDec (Blist * Bvector etn)
           (@pair_EqDec Blist (Bvector etn) eqdbl eqdbvn)) rb_oracle
        (@nil (Blist * Bvector etn));
      a0 <-$
      ([z, s']<-2 a;
       ([bits, _]<-2 z; $ ret bits) (list (Blist * Bvector etn))
         (@list_EqDec (Blist * Bvector etn)
            (@pair_EqDec Blist (Bvector etn) eqdbl eqdbvn)) rb_oracle s');
      z <-$ ([z, s']<-2 a0; x <-$ ret z; ret (x, s'));
      [_, state]<-2 z; ret hasInputDups state)
     (z <-$
      (GenUpdate_oc (k, v) blocksPerCall) (list (Blist * Bvector etn))
        (@list_EqDec (Blist * Bvector etn)
           (@pair_EqDec Blist (Bvector etn) eqdbl eqdbvn)) rb_oracle
        (@nil (Blist * Bvector etn)); [_, state]<-2 z; ret hasInputDups state)).
  { admit. }
  Print Ltac fcf_to_prhl_eq.
  Check comp_spec_eq_impl_eq.
  eapply test_same_goal2.

  (* Print Implicit test_same_goal. *)
  eapply test_same_goal'.

  Print Implicit (a <-$
      (oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbvn))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbvn)) (Oi_oc' i) 
         (0%nat, (k, v)) (replicate numCalls blocksPerCall))
        (list (Blist * Bvector etn)) (list_EqDec (pair_EqDec eqdbl eqdbvn))
        rb_oracle nil;
      a0 <-$
      ([z, s']<-2 a;
       ([bits, _]<-2 z; $ ret bits) (list (Blist * Bvector etn))
         (list_EqDec (pair_EqDec eqdbl eqdbvn)) rb_oracle s');
      z <-$ ([z, s']<-2 a0; x <-$ ret z; ret (x, s'));
      [_, state]<-2 z; ret hasInputDups state)
     (z <-$
      (GenUpdate_oc (k, v) blocksPerCall) (list (Blist * Bvector etn))
        (list_EqDec (pair_EqDec eqdbl eqdbvn)) rb_oracle nil;
      [_, state]<-2 z; ret hasInputDups state).

  (* apply test_same_goal'. *)
  (* TODO unification error?? I can't apply split_out_oracle_call either :-/ *)

  (* Intuitively, what's happening here? *)
  (* Want to prove: the probability of duplicates in the state is the same for both games. How should I prove that? *)
  (* Do the k and v matter? They shouldn't, because the oracle has been replaced with RB. But could there be skipping problems?? *)
  (* Should I do casework on `i`? What else can I do casework or induction on? Maybe induct on a list (the generalized maxCallsAndBlocks), with calls < i? (currently it is 0) and there would be casework on calls < i, calls = i, calls > i. ok, so i should generalize, then add IH and induct on list, then case on i...? the structure is actually quite similar to the proofs i did before about the ith calls. *)
  (* how to prototype this strategy and check if it will work? first, think through it on "paper" *)
  (*  *)
  
  (* unfold oracleCompMap_inner. *)
  Transparent Oi_oc'.
  unfold Oi_oc'.

  
Admitted.

(* get rid of oracle computation, transform GenUpdate_oc to GenUpdate_rb_inputs with hasDups on key and Vs explicitly
 ** hard? *)
(* note: no nat *)
Lemma Gi_rb_bad_eq_3 : 
  Pr [Gi_rb_bad_only_oracle] == Pr [Gi_rb_bad_no_oracle].
Proof.
  intros.
  fcf_to_prhl_eq.
  unfold Gi_rb_bad_only_oracle.
  unfold Gi_rb_bad_no_oracle.
  
Admitted.

Lemma well_formed_RndK : well_formed_comp RndK.
Proof. unfold RndK. fcf_well_formed. Qed.

Lemma well_formed_RndV : well_formed_comp RndV.
Proof. unfold RndV. fcf_well_formed. Qed.

Ltac wfk := apply well_formed_RndK.
Ltac wfv := apply well_formed_RndV.

(* DONE *)
(* get rid of k: never used as an input, and its output doesn't matter (easy?) *)
(* just bash way thru--need to line up the skips right *)
Lemma Gi_rb_bad_eq_4 : 
  Pr [Gi_rb_bad_no_oracle] == Pr [Gi_rb_bad_no_k].
Proof.
  intros.
  fcf_to_prhl_eq.
  unfold Gi_rb_bad_no_oracle.
  unfold Gi_rb_bad_no_k.
  unfold Instantiate.
  simplify.
  fcf_irr_l. wfk.
  simplify.
  fcf_skip_eq.
  simplify.
  unfold GenUpdate_rb_no_k.
  simplify.
  fcf_skip_eq.
  simplify.
  fcf_skip_eq.
  {
    clear H.
    revert blocksPerCall a a1.
    induction blocksPerCall as [ | blocks']; intros.
    - simplify. fcf_spec_ret.
    - simplify. fcf_skip_eq. fcf_skip_eq.
  }
  simplify.
  fcf_irr_l.
  simplify.
  fcf_spec_ret.
Qed.

(* go from GenUpdate* and Gen_loop* to compMap ** hard? *)
Lemma Gi_rb_bad_eq_5 : 
  Pr [Gi_rb_bad_no_k] == Pr [Gi_rb_bad_map].
Proof.
  intros.
  fcf_to_prhl_eq.
  unfold Gi_rb_bad_no_k.
  unfold Gi_rb_bad_map.
  unfold GenUpdate_rb_no_k.
(* unfold Gen_loop_rb_no_k. *)
(* fcf_to_prhl. *)

Admitted.

(* inline v' sample into compMap (easy?) *)
Lemma Gi_rb_bad_eq_6 : 
  Pr [Gi_rb_bad_map] == Pr [Gi_rb_bad_map_inline].
Proof.
  intros.
  fcf_to_prhl_eq.
  unfold Gi_rb_bad_map.
  unfold Gi_rb_bad_map_inline.
  fcf_skip_eq.

  (* did adam do this proof? could be annoying b/c v' appears in hasDups *)
  
  apply comp_spec_eq_symm.
  rewrite_r.
  (* get first two lines together *)
  instantiate (1 :=
                 (res <-$ (v' <-$ { 0 , 1 }^eta;
                          bits <-$
                               compMap eqdbv (fun _ : nat => { 0 , 1 }^eta)
                               (forNats (blocksPerCall - 1));
                          ret (v', bits));
                  [v', bits] <-2 res;
                  v'' <-$ { 0 , 1 }^eta;
                  ret hasDups eqdbl
                      ((to_list v'' ++ zeroes)
                         :: to_list a
                         :: to_list v'
                         :: map (fun v : Vector.t bool eta => to_list v) bits))).
  { prog_equiv. fcf_spec_ret. }

  fcf_skip.

Admitted.

(* get rid of key input (length-extended = no collisions) (easy?) *)
Lemma Gi_rb_bad_eq_7 : 
  Pr [Gi_rb_bad_map_inline] == Pr [Gi_rb_bad_map_no_keyinput].
Proof.
  intros.
  fcf_to_prhl_eq.
  unfold Gi_rb_bad_map_inline.
  unfold Gi_rb_bad_map_no_keyinput.
  fcf_skip_eq.
  fcf_skip_eq.

(* it changes from eqdbl to eqdbv? *)
(* anyway, should be able to reason that all other elements have the same len, so (v''||00) can't be a dup? might need vector info for that *)
  
Admitted.

(* inline v-sampling into compMap (easy?) *)
Lemma Gi_rb_bad_eq_8 : 
  Pr [Gi_rb_bad_map_no_keyinput] == Pr [Gi_rb_bad_map_inline_v].
Proof.
  intros.
  fcf_to_prhl_eq.
  unfold Gi_rb_bad_map_no_keyinput.
  unfold Gi_rb_bad_map_inline_v.


Admitted.

(* probability of bad event happening in RB game is bounded by the probability of collisions in a list of length (n+1) of randomly-sampled (Bvector eta) *)
Lemma Gi_rb_bad_collisions : forall (i : nat),
   Pr  [x <-$ Gi_rb_bad i; ret snd x ] <= Pr_collisions.
Proof.
  intros.
  rewrite Gi_rb_bad_eq_1.       (* done *)
  rewrite Gi_rb_bad_eq_2.       (* TODO hard *)
  rewrite Gi_rb_bad_eq_3.       (* TODO hard *)
  rewrite Gi_rb_bad_eq_4.       (* done *)
  rewrite Gi_rb_bad_eq_5.       (* TODO hard / questionable *)
  rewrite Gi_rb_bad_eq_6.       (* TODO easy *)
  rewrite Gi_rb_bad_eq_7.       (* TODO easy *)
  rewrite Gi_rb_bad_eq_8.       (* TODO easy *)
  unfold Gi_rb_bad_map_inline_v.
  
  Opaque hasDups.
  unfold Pr_collisions.
  Check dupProb.
  generalize dupProb.
  intros dupProb.

(* TODO there's a more general lemma *)
  assert (length (forNats (S blocksPerCall)) = S blocksPerCall).
  { apply forNats_length. }
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
  Print Gi_rf.
  (* Gi_prg uses oracleMap, Gi_rb and Gi_rf both use oracleCompMap (oracle box) *)
  rewrite Gi_normal_rb_eq. (* put Gi_prg into the same form using RB oracle *)
  (* TODO this might be wrong, maybe Gi_prg (S i) = Gi_rb (S i) *)
  (* shouldn't we be relating
     RB RB RF PRF with  <- Gi_rf 2
     RB RB RB PRF ? <-- Gi_prg 3 = Gi_rb 2
 *)

  rewrite Gi_rf_return_bad_eq. 
  rewrite Gi_rb_return_bad_eq. 
  rewrite Gi_rf_dups_return_bad_eq.

  (* NOTE still parametrized by i, so the hybrid matters *)
  rewrite Gi_rb_rf_identical_until_bad.
  (* unfold Gi_rb_bad. unfold PRF_Adversary. simplify. *)
  (* ??? shouldn't Pr_collisions depend on the hybrid. or just an upper bound? *)
  (* unfold Pr_collisions. *)
  (* rb oracle is queried when? i'm confused. only on ith call? yeah only on ith call (when RF is replaced with RB) *)
  (* so we "zoom in" here and it doesn't really matter if RB before it use new v... or if on the ith call we use new v... only the `bvector eta` getting generated matters? *)
  apply Gi_rb_bad_collisions.
Qed.

(* for above, want lemmas saying
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

(* TODO change this because I changed G2_prg *)
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