(* With backtracking resistance! *)

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

Print Comp.
SearchAbout Comp.
Locate "<-$". 

(* save the last v and output it as part of the state *)
Fixpoint Gen_loop (k : Bvector eta) (v : Bvector eta) (n : nat)
  : list (Bvector eta) * Bvector eta :=
  match n with
  | O => (nil, v)
  | S n' =>
    let v' := f k (Vector.to_list v) in
    let (bits, v'') := Gen_loop k v' n' in
    (v' :: bits, v'')           (* TODO change mine from (v ::) to (v ++), *or* prove indistinguishable (add another game in the beginning) *)
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
  v' <-$ {0,1}^eta;             (* is this actually unnecessary? *)
  [bits, v''] <-$2 Gen_loop_rb_intermediate k v' n;
  (* k' <-$ {0,1}^eta; *)
  ret (bits, (k, v'')).

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
  (* you really don't need tail here if you're going to use numCalls as an input *)
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

(* TODO: attempt to segment Gen_loop input-output list.

we want list (list (input * output)) = list (list (Blist * Bvector eta))?
but there are also oracle queries before and after it:
v, Gen_loop, k
so per call, a triple of (IO, list IO, IO)
and overall, list (IO, list IO, IO)?
that would be a lot easier to work with (would it?) 
and we can throw away the initial KV and the last KV 

ok, we don't need a triple, we can prove the list for each oracle call has at least 3 elements; i just want to segment by call

with this, the bad event would be (hasDups (combine-triple? (nth OracleCallState))) *)
(* Definition GenUpdate_oc_segment (state : KV) (n : nat) : *)
(*   OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) := *)
(*   [k, v_0] <-2 state; *)
(*   v <--$ (OC_Query _ (to_list v_0)); (* ORACLE USE *) *)
(*   [bits, v'] <--$2 Gen_loop_oc v n; *)
(*   (* but I don't have the oracle, so I can't pass it in explicitly and get Gen_loop_oc's end state. can I do this where I *do* have the oracle? *) *)
(*   (* TODO what's the state type here? and the global GenUpdate_oc return type? *) *)
(*   k' <--$ (OC_Query _ (to_list v' ++ zeroes)); (* ORACLE USE *) *)
(*   $ ret (bits, (k', v')). *)

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
  (* k' <--$ $ {0,1}^eta; *)
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
           (* this is an oracleComp, not an oracle *)
           (* the oracle has type (D * R) -> D -> Comp (R, (D * R)) *)
           (oracleComp : (nat * KV) -> D -> OracleComp OracleIn OracleOut (R * (nat * KV))) 
           (state : (nat * KV)) (* note this state type -- it is EXPLICITLY being passed around *)
           (inputs : list D) : OracleComp OracleIn OracleOut (list R * (nat * KV)) :=
  match inputs with
  | nil => $ ret (nil, state)
  | input :: inputs' => 
    [res, state'] <--$2 oracleComp state input;
      (* TODO: i want to segment after one of these calls. it passes the state onto the recursive call to use, then returns the result of that call -- but that state is the (nat * KV) pair. what about the input/output list? and what type do i want? 
but the type here is oraclecomp so by definition i can't access the oracle state... *)
    [resList, state''] <--$2 oracleCompMap_inner _ _ oracleComp state' inputs';
    (* wait, the results aren't in the right order -- need resList ++ [res] *)
    $ ret (resList ++ (res :: nil), state'')
  end.
(* compare to oc_compMap *)

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

Program Fixpoint segment {A : Type} (n : nat) (l : list A) {measure (length (skipn n l))}
  : list (list A) :=
  match l with
  | nil => nil
  | _ :: _ =>
    match n with
    | O => nil
    | S _ => firstn n l :: segment n (skipn n l)
    end
  end.
Solve All Obligations.
Next Obligation.
  simpl.
  destruct (skipn wildcard'1 wildcard'0). (* not true! obligations are too restrictive *)
  (* TODO: pretty sure this version terminates... *)
  admit.
  simpl.
  admit.
Qed.
Check segment.

(* Expose the bad events *)

(* Bad event *)
Definition dupsInIthCallInputs (i : nat) (state : list (Blist * Bvector eta)) : bool :=
  (* throw away outputs *)
  let inputs := fst (split state) in
  (* all the inputs are in one big list, so break it up by oracle call *)
  (* blocksPerCall inputs + 2 for the v and k re-updating *)
  let inputs_byCall := segment (blocksPerCall + 2) inputs in
  (* assumes ith element will exist, otherwise hasDups nil (default) = false *)
  let inputs_of_ith_call := nth i nil inputs_byCall in
  hasDups _ inputs_of_ith_call.

Definition dupsInIthCallInputs_only (i : nat) (inputs : list Blist) : bool :=
  (* all the inputs are in one big list, so break it up by oracle call *)
  (* blocksPerCall inputs + 2 for the v and k re-updating *)
  let inputs_byCall := segment (blocksPerCall + 2) inputs in
  (* assumes ith element will exist, otherwise hasDups nil (default) = false *)
  let inputs_of_ith_call := nth i nil inputs_byCall in
  hasDups _ inputs_of_ith_call.

(* ith game: use RF oracle *)
Definition Gi_rf_bad (i : nat) : Comp (bool * bool) :=
  [b, state] <-$2 PRF_Adversary i _ _ (randomFunc ({0,1}^eta) eqdbl) nil;
  ret (b, dupsInIthCallInputs i state). 

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
  ret (b, dupsInIthCallInputs i state). (* assumes ith element will exist, otherwise hasDups nil (default) = false *)

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

Print PRF_Advantage.
Print PRF_G_A.

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

Open Scope nat.
(* easier version: hardcoded l and i *)
Theorem Gi_normal_prf_eq_compspec_ez : forall (k1 k2 v : Bvector eta),
    (* i <= length l -> *)
   comp_spec
     (fun (x2 : list (list (Bvector eta)) * (nat * KV))
        (y : list (list (Bvector eta)) * (nat * KV) * unit) =>
      fst x2 = fst3 y)
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

  remember (1 :: 1 :: nil) as ls'.
  unfold oracleMap.
  simpl.
  fcf_inline_first.
  fcf_irr_l.
  fcf_inline_first.
  Print Oi_oc'.
  Print Oi_prg.
  (* TODO can I make GenUpdate_rb_intermediate and GenUpdate_rb_intermediate_oc simpler? *)
  fcf_skip. admit. admit.

fcf_inline_first.

(* back to compFold again, but what's the extra stuff happening in the latter? *)
(* the new output and state in compFold are useful! *)

fcf_simp.
fcf_inline_first.
remember (1 :: 1 :: nil) as ls'.
fcf_irr_r.                      (* why is this here? *)
fcf_inline_first.
fcf_irr_r.
fcf_simp.
simpl.
fcf_inline_first.
fcf_simp.
simpl.
fcf_inline_first.
fcf_simp.

(* ok, so it was equivalent?? what is all the extraneous stuff (and the irr's)? *)
(* but do they have the same b as output? they probably don't. what to do about this? *)
subst.


  (* unfold oracleMap. *)
  (* unfold oracleCompMap_inner. *)
  (* unfold Oi_prg. *)
  (* unfold Oi_oc'. *)

Admitted.

Theorem Gi_normal_prf_eq_compspec : forall (k1 k2 v : Bvector eta) (i : nat) l,
    i <= length l ->
   comp_spec
     (fun (x2 : list (list (Bvector eta)) * (nat * KV))
        (y : list (list (Bvector eta)) * (nat * KV) * unit) =>
      fst x2 = fst3 y)
     (oracleMap (pair_EqDec nat_EqDec eqDecState) (list_EqDec eqdbv)
        (Oi_prg i) (O, (k1, v)) l)
     ((oracleCompMap_inner
         (pair_EqDec (list_EqDec (list_EqDec eqdbv))
            (pair_EqDec nat_EqDec eqDecState))
         (list_EqDec (list_EqDec eqdbv)) (Oi_oc' i) 
         (O, (k2, v)) l) unit unit_EqDec (* note: k's differ. we aren't using this one *)
        (f_oracle f eqdbv k1) tt).
(* maybe i need to generalize the O in the initial state first? then will it be inductive? also, it is true?? i is hardcoded (should it be destructed?) and O is the starting value of callsSoFar *)
(* on paper: 
- inputs equal on callsSoFar < i, callsSoFar = i, and callsSoFar > i
  (and each depends on previous's inputs being equal)
- theorem about splitting on i and recombining the inputs?
- seems like a lot of work, but this kind of proof shows up a lot and this could be re-used
 *)
Proof.
  intros.
  (* destruct l. *)
  unfold oracleMap.
  unfold oracleCompMap_inner.
  unfold Oi_prg.
  (* also thm about compFold vs. oracleCompMap_inner? (maybe adam's version has useful theorems proven about it? what's its name?) *)
  unfold Oi_oc'.

(* should destruct l? and i? and callsSoFar ranges from 0 to (length l) - 1? *)

(* maybe just prove stuff about behavior of the Oi's? *)

Admitted.

Close Scope nat.
(* TODO make sure this is true, some important theorems depend on it *)
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

  fcf_inline_first.
  comp_skip.
  Opaque oracleMap.
  simpl.
  fcf_inline_first.

  remember x as k.
  fcf_irr_r. admit.             (* why is this here? *)
  fcf_inline_first.
  comp_skip.
  comp_simp.

  (* the z stuff simplifies into "A bits" *)
  (* comp_spec on the oracleMap and oracleCompMap_inner? *)
  simpl.
  fcf_inline_first.
  fcf_inline_first.
  fcf_to_prhl_eq.
  fcf_skip.

  instantiate (1 := fun x y => fst x = fst3 y).
  -
    Transparent oracleMap.
    apply Gi_normal_prf_eq_compspec.
    admit.                      (* TODO this assumption needs to be added everywhere *)

  - fcf_simp.
    simpl in H4.
    subst.
    simpl.
    fcf_inline_first.
    fcf_simp.
    fcf_inline_first.
    destruct u.
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

(* ------ *Identical until bad section *)
(* trying to figure out which OracleComps can be ignored (PRF_Adv, oracleCompMap_outer, _inner, Oi_oc, GenUpdate, Gen_loop) *)

(* TODO: might need to push these specs back further into Oi_oc and GenUpdate, then apply Adam's result in Gen_loop *)

(* TODO: might need to use oracle identical until bad? 
many layers of oraclecomps
oraclecomps: oraclecompmap_inner, Oi_oc', GenUpdate (various forms), Gen_loop
  (adam only has the equivalent of Gen_loop)
actual oracles: rb, rf

TODO: 
- discharge admit below
- figure out oracle id until bad
- figure out adam's proof of comp_spec

- figure out how to deal with call segmentation
- if there are no dups, then RF behaves exactly like RB -- key length extension doesn't matter, v doesn't matter? am i missing something? how do i show this?? 
no dups -> reason about RF match and RF state *)

  Definition randomFunc_withDups ls x :=
    y <-$ 
      (match (arrayLookup _ ls x) with 
        | Some y => ret y 
        | None => {0,1}^eta 
       end); 
    ret (y, (x, y) :: ls).

  (* TODO: add another game below replacing RF with RFWD in PRF_A. See PRF_DRBG.v *)
  (* Definition PRF_DRBG_G3_1 := *)
  (*   [b, _] <-$2 PRF_A _ _ (randomFunc_withDups) nil; *)
  (*   ret b. *)
  
(* version drilling down more, applying oracle eq until bad later. also fixed randomFunc *)
Theorem oracleCompMap__eq_until_bad : forall (i : nat) b b0,
    comp_spec
     (fun y1 y2 : list (list (Bvector eta)) * list (Blist * Bvector eta) =>
        let (bits_rb, state_rb) := y1 in
        let (bits_rf, state_rf) := y2 in
        let (inputs_rb, outputs_rb) := (fst (split state_rb), snd (split state_rb)) in
        let (inputs_rf, output_rf) := (fst (split state_rf), snd (split state_rf)) in

        dupsInIthCallInputs_only i inputs_rb = dupsInIthCallInputs_only i inputs_rf /\
        (dupsInIthCallInputs_only i inputs_rb = false ->
         bits_rb = bits_rf /\ state_rb = state_rf))
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
  (* eapply (fcf_oracle_eq_until_bad *)
  (*           (fun x => dupsInIthCallInputs_only i (fst (split x))) *)
  (*           (fun x => dupsInIthCallInputs_only i (fst (split x))) eq); intuition. *)
  intros.
  simpl.
  comp_skip.
  (* the ending computations are the same *)
  - instantiate (1 := (fun x1 x2 => x1 = x2)).
    (* TODO not true, use almost the same specification with dups and stuff *)
    (* returns: list (list (Bvector eta)) * (nat * KV) *
              list (Blist * Bvector eta) *)
    (* output bits, Oi_oc' state, and oracle input/output state *)

    unfold oracleCompMap_inner.
    (* do a smaller example? use adam's version? what stuff did he prove about it? *)
    SearchAbout oc_compMap.
    (* so Oi_oc' makes no sense without the i passed in from the state carried by oraclecompmap *)

    (* hasDups applies to GenUpdate. so, figure out how to relate
oracleCompMap/Oi_oc'+dupsInIthCalls with hasDups/GenUpdate

some kind of embedded postcondition? 

  match inputs with
  | nil => $ ret (nil, state)
        postcond: impossible, adversary has to make at least one call
  | input :: inputs' => 
    [res, state'] <--$2 oracleComp state input;
        postcond: if n = i then (same relation but with hasDups instead of dupsInIthCall)
                  else if n > i then ?
                  else if n < i then equality (they're running the RB computation)
        imagine we're just running this line, with some state (i, (k,v)). dups
    [resList, state''] <--$2 oracleCompMap_inner _ _ oracleComp state' inputs';
        postcond: ... related to the next?
    $ ret (resList ++ (res :: nil), state'')
        postcond: ... related to the prev?

needs to *relate* the two computations
can i induct on the number of calls?
how to reason about loops?
also is the oracle state accessible inside oracleCompMap_inner??

email adam about this (e.g. it messes with Pr[Collisions])
*)

    unfold Oi_oc'.
    
    admit.

  - fcf_simp.
    fcf_spec_ret.
    simpl.
    inversion H1.
    fcf_reflexivity.

    inversion H1.
    fcf_reflexivity.

    inversion H1.
    fcf_reflexivity.
Qed.
(* I have no idea what happened in the second case *)

(* should use hasDups instead, and randomFunc_withdups. not using them here so it'll unify / prove existing stuff *)
Theorem oracleCompMap__oracle_eq_until_bad : forall (i : nat) b b0,
    comp_spec
     (fun y1 y2 : list (list (Bvector eta)) * list (Blist * Bvector eta) =>
        (* TODO fix args *)
        (* let (bits_rb, state_rb) := y1 in *)
        (* let (bits_rf, state_rf) := y2 in *)
        (* let (inputs_rb, outputs_rb) := (fst (split state_rb), snd (split state_rb)) in *)
        (* let (inputs_rf, output_rf) := (fst (split state_rf), snd (split state_rf)) in *)
        dupsInIthCallInputs_only i (fst (split (snd y1))) = dupsInIthCallInputs_only i (fst (split (snd y2))) /\
        (dupsInIthCallInputs_only i (fst (split (snd y1))) = false ->
         snd y1 = snd y2 /\ fst y1 = fst y2))

        (* hasDups _ (fst (split (snd y1))) = hasDups _ (fst (split (snd y2))) /\ *)
        (* (hasDups _ (fst (split (snd y1))) = false -> *)
        (*  snd y1 = snd y2 /\ fst y1 = fst y2)) *)

        (* hasDups _ inputs_rb = hasDups _ inputs_rf /\ *)
        (* (hasDups _ inputs_rb = false -> *)
        (*  bits_rb = bits_rf /\ state_rb = state_rf)) *)

     (* could this be true if oracleCompMap_inner ignored the passed-in oracles and somehow violated the conditions? *)
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
        (randomFunc ({0,1}^eta) eqdbl) nil).
Proof.
  intros.
  (* TODO review this *)
  eapply (fcf_oracle_eq_until_bad
            (fun x => dupsInIthCallInputs_only i (fst (split x)))
            (fun x => dupsInIthCallInputs_only i (fst (split x))) eq); intuition.

 - fcf_well_formed. admit.
  - intros. unfold rb_oracle. fcf_well_formed.
  - intros. unfold randomFunc. destruct (arrayLookup eqdbl a b1); fcf_well_formed.
  - 
    subst.
    unfold randomFunc, rb_oracle.
    (* need to make a version of randomFunc that adds the input to the state, even when we find it. *)
    (* It still looks like dupsInIthCollInputs_only may be more complicated than necessary (for this proof, at least).  The arguments below assume we have replaced it with hasDups. *)

    (* Once that is done, we just need to case split *)
    case_eq (arrayLookup eqdbl x2 a); intuition.
    (* bad case *)
    fcf_irr_l.
    fcf_spec_ret.
    simpl.
    remember (split x2) as z.
    destruct z.
    simpl.
    (* Once we switch to a version of randomFunc that keeps track of duplicate calls, we can show that both sides of the equation are true because when we have (a :: l), and when we have (arrayLookup a l = Some b1) *)
    admit.

    simpl in H3.
    remember (split x2) as z. destruct z.
    simpl in *.
    (* contradiction in hypotheses, hasDups (a :: l) = false, but we know a is in l *)
    admit.
    (* same contradiction *)
    admit.

    (* not bad case---equality is perserved *)
    fcf_skip.
    fcf_spec_ret.

    - (* once we have duplicates, we will always have duplicates.  *)
      admit.
    - (*same as above *)
      admit.
Qed.

(* TODO: this is the real lemma *)
(* TODO: perhaps we should use comp_spec with **hasDups* for inner PRF_DRBG and prove that that implies comp_spec with dupsInIthCallInputs *)
Theorem PRF_Adv_eq_until_bad : forall (i : nat),
   comp_spec 
     (fun a b : bool * list (Blist * Bvector eta) =>
        let (adv_rb, state_rb) := a in
        let (adv_rf, state_rf) := b in
        let (inputs_rb, outputs_rb) := (fst (split state_rb), snd (split state_rb)) in
        let (inputs_rf, output_rf) := (fst (split state_rf), snd (split state_rf)) in
        dupsInIthCallInputs i state_rb = dupsInIthCallInputs i state_rf /\
        (dupsInIthCallInputs i state_rb = false ->
         (* true -- if there are no duplicates, then the random function behaves exactly like RB, so the key is randomly sampled AND the v (going into the PRF) is also randomly sampled. so the outputs should be the same.

in fact, if there are no dups, PRF_Adv rf i = PRF_Adv rb i.

so, this means the comp_spec above is true?

does PRHL act like giving each the same "tape" of randomness for equality? *)
         state_rb = state_rf /\ adv_rb = adv_rf))
     ((PRF_Adversary i) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv)) rb_oracle nil)
     ((PRF_Adversary i) (list (Blist * Bvector eta))
        (list_EqDec (pair_EqDec eqdbl eqdbv))
        (randomFunc ({ 0 , 1 }^eta) eqdbl) nil).
Proof.
  intros.
  unfold PRF_Adversary.
  simpl.
  fcf_inline_first.
  fcf_skip.
  fcf_simp.
  (* simpl. *)
  (* this just pushed the lemma back further into here -- what should this spec be?? *)
  fcf_skip.
  apply oracleCompMap__oracle_eq_until_bad. (* pretty sure this is correct *)

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

  case_eq (dupsInIthCallInputs i state_rb_); intuition.

  (* duplicates exist, computations are irrelevant *)
  - 
    fcf_irr_l.
    fcf_irr_r.
    rename a into adv_rb_.
    rename b1 into adv_rf_.
    fcf_spec_ret.
    (* true=false in hypotheses *)
    (* dupsInIthCallInputs i state_rb_ = true (by case_eq) and false (by assumption in postcondition) *)
    congruence.

  (* no duplicates, equality is preserved *)
  (* automatically applied dups = false to get that the states and outputs are the same *)
  - simpl in *.
    subst.
    fcf_skip.
    fcf_spec_ret.
Qed.

  (* My old attempt *)
(*
  simpl in H3.
  destruct b2.
  intuition.
  
  remember a0 as bits_rb.
  remember l as bits_rf.

  (* need to show that adversary can't distinguish the bits -- are they the same? *)
  (* see H5 *)
  
  fcf_skip.
  (* TODO: look at proof of PRF_A_randomFunc_eq_until_bad *)

  - instantiate (1 := (fun x y => x = y)). (* eq -- for testing, not sure if right *)
    (* if this isn't right, what assumption do i need? *)
    simpl in *.
    (* might need to use oracle id until bad? *)
    (* TODO *)

    admit.

  - simpl in *.
    subst.
    fcf_spec_ret.
Qed.
*)

(* First assumption for id until bad: the two games have the same probability of returning bad *)
(* uses provided oracle on call number i
   i = 2
                      0  1  2   3   4
   Gi_rf_bad i =     RB RB RF PRF  PRF
   Gi_rb_bad i =     RB RB RB PRF PRF
   bad event = duplicates in input on call number i *)
Lemma Gi_rb_rf_return_bad_same :  forall (i : nat),
    Pr  [x <-$ Gi_rb_bad i; ret snd x ] ==
    Pr  [x <-$ Gi_rf_bad i; ret snd x ].
Proof.
  intros.
  unfold Gi_rb_bad. unfold Gi_rf_bad.
  fcf_to_prhl_eq.
  fcf_inline_first.
  fcf_skip.
  (* different spec if you do `fcf_to_prhl` only, and in this location *)
  *
    Check PRF_Adv_eq_until_bad.
    apply PRF_Adv_eq_until_bad.
    (* is it true? this doesn't include the dupsInNthInput stuff. but do we even need that if the RB stuff beforehand is the same? *)
    (* only difference: one uses rb_oracle, other uses randomFunc oracle *)
  *
    destruct b0.
    intuition.
    fcf_simp.
    rewrite H2.
    simpl.
    fcf_reflexivity.
Qed.

(* "distribution of the value of interest is the same in c_1 and c_2 when the bad event does not happen" -- the two are basically the same if the bad event doesn't happen, so it's true.
         differences: 1. PRF re-keyed using RF vs. randomly sampled. but PRF re-keyed using something of length > eta, so it is effectively randomly sampled.
         2. the v going into the next call (if it exists) is randomly sampled vs. resulting from a RF call, but it doesn't matter *)

Theorem Gi_rb_rf_no_bad_same : forall (i : nat) (a : bool),
   evalDist (Gi_rb_bad i) (a, false) == evalDist (Gi_rf_bad i) (a, false).
Proof.
  intros.
  fcf_to_prhl.                  (* note the auto-specification here *)
  (* it's NOT fcf_to_prhl_eq *)
  unfold Gi_rb_bad.
  unfold Gi_rf_bad.
  fcf_skip.
  *
    apply PRF_Adv_eq_until_bad.
    (* but is this the right specification? *)
  *
    fcf_simp.
    intuition.
    fcf_spec_ret.

    pairInv.
    apply H3 in H6.
    intuition.
    subst.
    reflexivity.

    pairInv.
    rewrite H2.
    rewrite <- H2 in H6.
    apply H3 in H6.
    intuition.
    subst.
    fcf_reflexivity.
Qed.

(* Applying the fundamental lemma here *)
Lemma Gi_rb_rf_identical_until_bad : forall (i : nat),
| Pr[x <-$ Gi_rf_bad i; ret fst x] - Pr[x <-$ Gi_rb_bad i; ret fst x] | <=
                                              Pr[x <-$ Gi_rb_bad i; ret snd x].
Proof.
  intros. rewrite ratDistance_comm.
  fcf_fundamental_lemma.
  Check fundamental_lemma_h.

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
  ret (dupsInIthCallInputs i state).

(* throw away all other inputs but the ones in the "ith" call ((k,v) are randomly sampled going into the hybrid ith call anyway) 
TODO: make sure numbering is right and that the ith call exists, etc. *)
Definition Gi_rb_bad_only_oracle : Comp bool :=
  [k, v] <-$2 Instantiate;
  [_, state] <-$2 GenUpdate_oc (k, v) blocksPerCall _ _ rb_oracle nil;
  (* there is only 1 call, so segment will return 1 list, and we get that (the 1st one) *)
  ret (dupsInIthCallInputs O state).

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
  apply Gi_prf_rf_close.
  apply Gi_rf_rb_close.
Check Gi_rf_rb_close.
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
  admit.
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

(* Adversary, split into two *)
Parameter A1 : Comp nat.
Parameter A2 : list (list (Bvector eta)) -> KV -> Comp bool.
(* Also the adversary is slightly different from the one above. How do we re-use the adv? *)

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
  v'' <- f k (to_list v');
  A2 (head_bits :: tail_bits) (k', v''). 

(* A2 still cannot distinguish *)
(* how do I reuse the previous work? it depended on the adversary result, it wasn't an equivalence rewriting on the inside two lines *)
(* how would i even do this proof from scratch? would have to prove that PRF -> RF and RF -> RB yield equivalence etc. for A2 bits (k, v') <-- state *)
(* also, what about the extra UpdateV probabilities? *)
Definition G1a_br : Comp bool :=
  [k, v] <-$2 Instantiate;
  bits <-$ compMap _ GenUpdate_rb maxCallsAndBlocks;
  v' <-$ {0,1}^eta;              (* this should also be replaced? *)
  (* was formerly v' <- f k v; *)
  A2 bits (k, v'). 

(* ideal world *)
(* 1a and 2: v ~ {0,1} -> f v ~ {0,1}? maybe assume it *)
(* or add an extra PRF_Advantage (random k -> f k v yields random v') *)
Definition G2_br : Comp bool :=
  [k, v] <-$2 Instantiate;
  bits <-$ compMap _ GenUpdate_rb maxCallsAndBlocks;
  A2 bits (k, v).

(* 2 and 2a are clearly equivalent? (k,v) gives no information about bits, so remove k, v *)
(* this is where the indistinguishability proof ends -- don't know how to use this as an intermediate stage. is it possible to do G1_br ->(?) G1_prg -> G2_prg -> G2_br? *)

(* Definition G1_prg : Comp bool :=
  [k, v] <-$2 Instantiate;
  [head_bits, state'] <-$2 GenUpdate_noV (k, v) blocksPerCall;
  [tail_bits, _] <-$2 oracleMap _ _ GenUpdate state' (tail maxCallsAndBlocks);
  A (head_bits :: tail_bits).

Definition G2_prg : Comp bool :=
  bits <-$ compMap _ GenUpdate_rb maxCallsAndBlocks;
  A bits. *)

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