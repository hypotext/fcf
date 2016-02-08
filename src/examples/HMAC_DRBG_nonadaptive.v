Set Implicit Arguments.

Require Import FCF.
(* RndInList has a useful theorem (qam_count) about counting calls to an oracle. *)
Require Import RndInList.
Require Import HasDups.
Require Import CompFold.
Require Import PRF.
Require Import OracleHybrid.
Require Import List.

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

- Write out all subgames (e.g. involving random functions)
- Review step 4 and OracleHybrid proofs
- Remove unneeded GenUpdate*_oc versions

- Prove G1 = Gi 0 and G2 = Gi q
- Prove Gi_prf (S i) = Gi_prg i
- Prove PRF advantage theorems
- Prove the theorems: (figure out what the main lemmas and difficulties are)
  - Pr[Collisions] = ? (for n+1 calls)
  - Outer base case (Adam's proof)
  - Outer inductive hypothesis
  - Inner double induction (Adam's proof) -- PRF_DRBG argument

- Prove other things (well-formedness, etc. -- the hypotheses)
  - Deal with actual Instantiate (not just RB)
- Add backtracking resistance and prove that 
- Change to adaptive adversary?? (additional input, etc.)
*)

Local Open Scope list_scope.
Local Opaque evalDist.

Section PRG.

  (* note: the domain of the f is now Blist, not an abstract D
the key type is now also Bvector eta, since HMAC specifies that the key has the same size as the output (simplified) *)
Variable eta : nat.

Variable RndK : Comp (Bvector eta).
Variable RndV : Comp (Bvector eta).

Variable f : Bvector eta -> Blist -> Bvector eta.

Definition KV : Set := (Bvector eta * Bvector eta)%type.
Hypothesis eqDecState : EqDec KV.
Variable eqdbv : EqDec (Bvector eta).
Variable eqdbl : EqDec Blist.

(* injection is Vector.to_list. TODO prove this *)
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

(* save the last v and output it as part of the state *)
Fixpoint Gen_loop (k : Bvector eta) (v : Bvector eta) (n : nat)
  : list (Bvector eta) * Bvector eta :=
  match n with
  | O => (nil, v)
  | S n' =>
    let v' := f k (Vector.to_list v) in
    let (bits, v'') := Gen_loop k v' n' in
    (v' :: bits, v'')
  end.

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

Definition GenUpdate_rb_intermediate (state : KV) (n : nat) 
  : Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  v'' <-$ {0,1}^eta;
  [bits, v'] <-$2 Gen_loop_rb_intermediate k v n;
  k' <-$ {0,1}^eta;
  ret (bits, (k', v'')).

(* final versions (without unnecessary (k, v) updating) *)
Fixpoint Gen_loop_rb (n : nat) : Comp (list (Bvector eta)) :=
  match n with
  | O => ret nil
  | S n' =>
    v' <-$ {0,1}^eta;
    bits <-$ Gen_loop_rb n';
    ret (v' :: bits)
  end.

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
(* used with oracleMap: call the oracle numCalls times, each time requesting blocksPerCall blocks *)

(* only first call uses GenUpdate_noV; assumes numCalls > 0 *)
Definition G1_prg : Comp bool :=
  [k, v] <-$2 Instantiate;
  [head_bits, state'] <-$2 GenUpdate_noV (k, v) blocksPerCall;
  [tail_bits, _] <-$2 oracleMap _ _ GenUpdate state' (tail maxCallsAndBlocks);
  A (head_bits :: tail_bits).

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
  [k, v] <-$2 Instantiate;
  [bits, _] <-$2 oracleMap _ _ GenUpdate_rb_oracle tt maxCallsAndBlocks;
  A bits.

(* simpler version of GenUpdate only requires compMap. prove the two games equivalent *)
Definition G2_prg : Comp bool :=
  [k, v] <-$2 Instantiate;
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
  let GenUpdate_choose := if lt_dec callsSoFar i (* callsSoFar < i *)
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
Fixpoint Gen_loop_oc (v : Bvector eta) (n : nat)
  : OracleComp (list bool) (Bvector eta) (list (Bvector eta) * Bvector eta) :=
  match n with
  | O => $ ret (nil, v)
  | S n' =>
    v' <--$ (OC_Query _ (to_list v)); (* ORACLE USE *)
    [bits, v''] <--$2 Gen_loop_oc v' n';
    $ ret (v' :: bits, v'')
  end.

(* takes in key but doesn't use it, to match the type of other GenUpdates *)
Definition GenUpdate_oc (state : KV) (n : nat) :
  OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) :=
  [k, v_0] <-2 state;
  v <--$ (OC_Query _ (to_list v_0)); (* ORACLE USE *)
  [bits, v'] <--$2 Gen_loop_oc v n;
  k' <--$ (OC_Query _ (to_list v' ++ zeroes)); (* ORACLE USE *)
  $ ret (bits, (k', v')).

(* doesn't use the oracle *)
Definition GenUpdate_noV_oc (state : KV) (n : nat) :
  OracleComp (list bool) (Bvector eta)  (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  [bits, v'] <-2 Gen_loop k v n;
  k' <- f k (to_list v' ++ zeroes);
  $ ret (bits, (k', v')).

(* doesn't use the oracle, uses the PRF *)
Definition GenUpdate_PRF_oc (state : KV) (n : nat) :
  OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  v' <- f k (to_list v);
  [bits, v''] <-2 Gen_loop k v' n;
  k' <- f k (to_list v' ++ zeroes);
  $ ret (bits, (k', v'')).

(* doesn't use the oracle *)
(* intermediates have unnecessary state and updating of the state to match earlier ones *)
Definition GenUpdate_rb_intermediate_oc (state : KV) (n : nat) 
  : OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  v'' <--$ $ {0,1}^eta;
  [bits, v'] <--$2 $ Gen_loop_rb_intermediate k v n;
  k' <--$ $ {0,1}^eta;
  $ ret (bits, (k', v'')).

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
Definition Oi_oc' (i : nat) (sn : nat * KV) (n : nat) 
  : OracleComp Blist (Bvector eta) (list (Bvector eta) * (nat * KV)) :=
  [callsSoFar, state] <-2 sn;
  [k, v] <-2 state;
  let GenUpdate_choose := 
      if lt_dec callsSoFar i (* callsSoFar < i *)
      then GenUpdate_rb_intermediate_oc
      else if beq_nat callsSoFar i (* callsSoFar = i *)
           then GenUpdate_oc    (* uses provided oracle (PRF or RF) *)
      else if beq_nat callsSoFar O 
           then GenUpdate_noV_oc  (* first call does not update v *)
      else GenUpdate_PRF_oc in        (* uses PRF with (k,v) updating *)
  [bits, state'] <--$2 GenUpdate_choose (k, v) n;
  $ ret (bits, (S callsSoFar, state')).

(* oracleCompMap_inner repeatedly applies the given oracle on the list of inputs (given an initial oracle state), collecting the outputs and final state *)
Fixpoint oracleCompMap_inner {D R OracleIn OracleOut : Set} 
           (e1 : EqDec ((list R) * (nat * KV))) 
           (e2 : EqDec (list R)) 
           (oracleComp : (nat * KV) -> D -> OracleComp OracleIn OracleOut (R * (nat * KV))) (state : (nat * KV))
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

(* Expose the bad events *)
(* ith game: use RF oracle *)
Definition Gi_rf_bad (i : nat) : Comp (bool * bool) :=
  [b, state] <-$2 PRF_Adversary i _ _ (randomFunc ({0,1}^eta) eqdbl) nil;
  let rfInputs := fst (split state) in
  ret (b, hasDups _ (nth i nil rfInputs)). (* assumes ith element will exist, otherwise hasDups nil (default) = false *)

Definition Gi_rb (i : nat) : Comp bool :=
  let rb_oracle := (fun state input =>
                    output <-$ ({0,1}^eta);
                    ret (output, (input, output) :: state)) in
  [b, state] <-$2 PRF_Adversary i _ _ rb_oracle nil;
  let rbInputs := fst (split state) in
  ret b.

(* adam wrote a new game here -- bad event is repetition in the random INPUTS
INPUTS = v :: (first n of outputs)? *)
(* pass in the RB oracle that records its inputs
what about preceding/following RB and (especially) PRF inputs/outputs? *)
Definition Gi_rb_bad (i : nat) : Comp (bool * bool) :=
  let rb_oracle := (fun state input =>
                    output <-$ ({0,1}^eta);
                    ret (output, (input, output) :: state)) in
  [b, state] <-$2 PRF_Adversary i _ _ rb_oracle nil;
  let rbInputs := fst (split state) in
  ret (b, hasDups _ (nth i nil rbInputs)). (* assumes ith element will exist, otherwise hasDups nil (default) = false *)

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
PRF_Advantage 0 = 0

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

(* these proofs will require dealing with OracleComps *)
Lemma PRF_Advantage_0 : 
    PRF_Advantage_Game numCalls = 0.
Proof.
  intros. unfold PRF_Advantage_Game. unfold PRF_Advantage.

  assert (distance_0_eq : forall G1 G2, | Pr[G1] - Pr[G2] | = 0 <-> Pr[G1] == Pr[G2]).
  { intros. intuition. admit.
    (* rewrite -> H. ?? *) admit. } (* TODO this is probably already proven *)

  apply distance_0_eq. clear distance_0_eq.
  
  fcf_to_prhl_eq. (* TODO when should I *not* use this? *)

  (* TODO lemma that PRF_Advantage_Game numCalls always uses random bits and ignores the inputted oracle, so games A and B are on indistinguishable output *)

  unfold PRF_Adversary.
  unfold PRF_G_A.
  unfold PRF_G_B.

  fcf_irr_l. admit.

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

    admit.

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

Lemma PRF_Advantages_same : forall (i j : nat),
    i <> numCalls -> j <> numCalls ->
    PRF_Advantage_Game i = PRF_Advantage_Game j.
Proof.
  intros i j i_neq j_neq.
  unfold PRF_Advantage_Game. unfold PRF_Advantage.
  
Admitted.

Lemma PRF_Advantages_lte : forall (i : nat),
    PRF_Advantage_Game i <= PRF_Advantage_Game 0.
Proof.
  intros.
  (* TODO finish this using above two lemmas *)
  (* destruct (beq_nat i numCalls). *)

Admitted.

(* base case theorem (adam's) TODO *)

(* Step 1 *)
(* let i = 3. 
Gi_prf i: RB RB PRF PRF PRF
Gi_rf i:  RB RB RF  PRF PRF 
need to use `Gi_prf i` instead of `Gi_prg i` because this matches the form of 
`Gi_rf` closer so we can match the form of PRF_Advantage*)
Lemma Gi_prf_rf_close_i : forall (i : nat),
  | Pr[Gi_prf i] - Pr[Gi_rf i] | <= PRF_Advantage_Game i.
Proof.
  intros i.
  unfold PRF_Advantage_i.
  (* don't need to unfold *)
  unfold Gi_prf.
  unfold Gi_rf.
  unfold PRF_Advantage_Game.
  reflexivity. (* TODO how was this proven automatically? *)
Qed.

Lemma Gi_prf_rf_close : forall (i : nat),
  | Pr[Gi_prf i] - Pr[Gi_rf i] | <= PRF_Advantage_i.
Proof.
  intros.
  eapply leRat_trans.
  apply Gi_prf_rf_close_i.
  apply PRF_Advantages_lte.
Qed.

(* ------------------------------- *)

(* Step 2 *)

(* TODO use Adam's existing theorem. not sure if this is the right bound.
should be a function of [blocksPerCall + 1] (for the extra v-update) *)
Definition Pr_collisions := (S blocksPerCall)^2 / 2^eta.

(* may need to update this w/ new proof *)
Definition Gi_Gi_plus_1_bound := PRF_Advantage_i + Pr_collisions.

(* Random functions to random bits -- what's the bound? what are the intermediate games? 
need to look at step 4 again *)
(* TODO make sure this is true, some important theorems depend on it *)
(* this moves from the normal adversary to the PRF adversary (which depends on the prev.) *)
Lemma Gi_normal_prf_eq : forall (i : nat),
    Pr[Gi_prg i] == Pr[Gi_prf (S i)].
Proof.
  intros.
  unfold Gi_prg.
  unfold Gi_prf.
Admitted.

Lemma Gi_rf_return_bad_eq : forall (i : nat),
    Pr[Gi_rf i] == Pr[x <-$ Gi_rf_bad i; ret fst x].
Proof.
Admitted.

Lemma Gi_rb_return_bad_eq : forall (i : nat),
    Pr[Gi_rb i] == Pr[x <-$ Gi_rb_bad i; ret fst x].
Proof.
Admitted.

(* does not hold for i = 0:
Gi_prg 0: PRF PRF PRF...
Gi_prg 1: RB PRF PRF...
Gi_rb 1 : RB PRF PRF... *)
Lemma Gi_normal_rb_eq : forall (i : nat),
    Pr[Gi_prg (S i)] == Pr[Gi_rb i].
Proof.
  intros.
  unfold Gi_prg.
  unfold Gi_rb.
Admitted.

(* ------ Identical until bad section *)

(* First assumption for id until bad: the two games have the same probability of returning bad *)
Lemma Gi_rb_rf_return_bad_same :  forall (i : nat),
    Pr  [x <-$ Gi_rb_bad i; ret snd x ] ==
    Pr  [x <-$ Gi_rf_bad (S i); ret snd x ].
Proof.
  intros.
  unfold Gi_rb_bad. unfold Gi_rf_bad.
  simpl.
  fcf_inline_first.
  fcf_skip.
  fcf_skip.
  fcf_simp.
  fcf_skip.
  fcf_to_prhl.              (* true? *)
  * admit.
  * clear H1 H H0. (* as a test; don't actually clear these *)
    fcf_simp.
    fcf_inline_first.
    fcf_skip.
    simpl.
    fcf_simp.
    simpl.
    destruct i.
    fcf_reflexivity.
    fcf_reflexivity.
(* did this use the comp_spec relation proved before it? maybe implicitly? *)
Qed.

      (* "distribution of the value of interest is the same in c_1 and c_2 when the bad event does not happen" -- the two are basically the same if the bad event doesn't happen, so it's true.
         differences: 1. PRF re-keyed using RF vs. randomly sampled. but PRF re-keyed using something of length > eta, so it is effectively randomly sampled.
         2. the v going into the next call (if it exists) is randomly sampled vs. resulting from a RF call, but it doesn't matter 

TODO need one of those complex comp_specs *)
Theorem Gi_rb_rf_no_bad_same : forall (i : nat) (a : bool),
   evalDist (Gi_rb_bad i) (a, false) == evalDist (Gi_rf_bad (S i)) (a, false).
Proof.
  intros.
  fcf_to_prhl.
  unfold Gi_rb_bad.
  unfold Gi_rf_bad.
Admitted.

Lemma Gi_rb_rf_identical_until_bad : forall (i : nat),
| Pr[x <-$ Gi_rf_bad (S i); ret fst x] - Pr[x <-$ Gi_rb_bad i; ret fst x] | <=
                                              Pr[x <-$ Gi_rb_bad i; ret snd x].
Proof.
  intros. rewrite ratDistance_comm.
  fcf_fundamental_lemma.

  (* first assumption: they have same probability of returning bad *)
  - apply Gi_rb_rf_return_bad_same.
    
  (* "distribution of the value of interest is the same in c_1 and c_2 when the bad event does not happen" *)
  - apply Gi_rb_rf_no_bad_same.
Qed.

(* ----------- End identical until bad section *)

  (* first, is this true? (lemma about probability of bad event) *)
(* since i defined the bad event as focusing on the ith output, i should be able to prove that all output after i (PRF output) is irrelevant and we only care about the random input from previous calls *)

(* does this deal with the additional v? yes (is an input to oracle). and the key updating? 
why do we need the fact that from the previous call the key was randomly sampled? *)
  (* TODO figure out how to apply adam's result here *)
Lemma Gi_rb_bad_collisions : forall (i : nat),
   Pr  [x <-$ Gi_rb_bad i; ret snd x ] <= Pr_collisions.
Proof.
  unfold Gi_rb_bad.
  unfold PRF_Adversary.
  unfold Oi_oc'.
  unfold GenUpdate_oc.
  simpl.
  fcf_inline_first.
Admitted.

(* Main theorem (modeled on PRF_DRBG_G3_G4_close) *)
(* Gi_rf 0:  RF  PRF PRF
Gi_prg 0:    PRF PRF PRF

Gi_rf  1:    RF  PRF PRF
Gi_prg 1:    RB  PRF PRF

Gi_rf  2:    RB  RF  PRF 
Gi_prg 2:    RB  RB  PRF *)
Lemma Gi_rf_rb_close : forall (i : nat), (* not true for i = 0 (and not needed) *)
  | Pr[Gi_rf (S i)] - Pr[Gi_prg (S i)] | <= Pr_collisions.
Proof.
  intros.
  rewrite Gi_normal_rb_eq. (* put Gi_prg into the same form using RB oracle *)

  rewrite Gi_rf_return_bad_eq. 
  rewrite Gi_rb_return_bad_eq. 

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
  rewrite Gi_normal_prf_eq.
  apply Gi_prf_rf_close.
  apply Gi_rf_rb_close.
Qed.

(* ------------------------------- *)

(* this proof (in OracleHybrid) is long and uses identical until bad. should i make sure this is true first? *)
(* TODO make sure the numbering is right *)
Lemma G1_Gi_O_equal :
  Pr[G1_prg] == Pr[Gi_prg O].
Proof.
  unfold G1_prg.
  unfold Gi_prg.
  simpl.
  comp_skip.
  (* fcf_simp. *)
  
  (* unfold oracleMap. *)
  (* unfold compFold. *)
  
  (* fcf_to_prhl. *)

Admitted.

Lemma G2_oracle_eq :
  Pr[G2_prg'] == Pr[G2_prg]. (* oracleCompMap vs compMap *)
Proof.
  unfold G2_prg, G2_prg'.
  comp_skip.
(* relate GenUpdate_rb and GenUpdate_rb_oracle *)

Admitted.

Lemma G2_Gi_n_equal :
  Pr[G2_prg] == Pr[Gi_prg numCalls].
Proof.
  rewrite <- G2_oracle_eq.
  unfold G2_prg'.
  unfold Gi_prg.
  comp_skip.
  (* comp_skip. (* ? *) *)

Admitted.

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
