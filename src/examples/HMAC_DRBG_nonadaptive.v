Set Implicit Arguments.

Require Import FCF.
(* RndInList has a useful theorem (qam_count) about counting calls to an oracle. *)
Require Import RndInList. 
Require Import HasDups.
Require Import CompFold.
Require Import PRF.
Require Import OracleHybrid.

  (* TODO:

- Blist definitions X
- New for PRF-DRBG etc functions (instantiate, generate, update) X
- Make the correct oracles X
- Fill in the oracles with functions X

- Write the initial game and final game X
- Write the game i X
- Construct PRF adversary (X?)
- Write the theorem statements (final theorem, inductive hypothesis) (in progress)

- Prove G1 = Gi 0 and G2 = Gi q
- Prove the theorems:
  - maintain state from prev call of GenUpdate
  - Pr[Collisions] = ? (for n+1 calls)
  - Outer base case (Adam's proof)
  - Outer inductive hypothesis
  - Inner double induction (Adam's proof)
- Prove other things (well-formedness, etc. -- the hypotheses)
  - Deal with actual Instantiate
- Add backtracking resistance and prove that *)

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

(* injection is Vector.to_list. TODO prove this *)
Variable injD : Bvector eta -> Blist.
Hypothesis injD_correct :
  forall r1 r2, injD r1 = injD r2 -> r1 = r2.

Definition to_list (A : Type) (n : nat) (v : Vector.t A n) := Vector.to_list v.

(* PRG functions *)

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
  let v'l := to_list v' in
  k' <- f k (v'l ++ zeroes);
  v'' <- f k' (v'l);
  ret (bits, (k', v'')).

(* want to change to this, and prove the outputs are the same. 
the other GenUpdates don't use this version *)
Definition GenUpdate (state : KV) (n : nat) :
  Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  v' <- f k (to_list v);
  [bits, v''] <-2 Gen_loop k v' n;
  k' <- f k (to_list v' ++ zeroes);
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

Variable blocksPerUpdate : nat.       (* blocks generated by GenLoop *)
Variable numCalls : nat.        (* number of calls to GenUpdate *)
Definition maxCallsAndBlocks : list nat := replicate numCalls blocksPerUpdate.
(* used with oracleMap: call the oracle numCalls times, each time requesting blocksPerUpdate blocks *)

Definition G1_prg : Comp bool :=
  [k, v] <-$2 Instantiate;
  [bits, _] <-$2 oracleMap _ _ GenUpdate (k, v) maxCallsAndBlocks;
  A bits.

(* TODO: intermediate games with random functions and random bits *)

Definition G2_prg' : Comp bool :=
  [k, v] <-$2 Instantiate;
  [bits, _] <-$2 oracleMap _ _ GenUpdate_rb_oracle tt maxCallsAndBlocks;
  A bits.

(* simpler version of GenUpdate only requires compMap. prove the two games equivalent *)
Definition G2_prg : Comp bool :=
  [k, v] <-$2 Instantiate;
  bits <-$ compMap _ GenUpdate_rb maxCallsAndBlocks;
  A bits.

Check G1_G2_close.

(* oracle i *)
(* number of calls starts at 0 and ends at q. 
G0: PRF PRF PRF
G1: RB  PRF PRF
G2: RB  RB  PRF
G2: RB  RB  RB *)
Definition Oi_prg (i : nat) (sn : nat * KV) (n : nat)
  : Comp (list (Bvector eta) * (nat * KV)) :=
  [numCalls, state] <-2 sn;
  let GenUpdate_choose := if lt_dec numCalls i (* numCalls < i *)
                          then GenUpdate_rb_intermediate
                          (* first call does not update v, to make proving equiv. easier*)
                          else if beq_nat numCalls O then GenUpdate_noV
                               else GenUpdate in
  (* note: have to use intermediate, not final GenUpdate_rb here *)
  [bits, state'] <-$2 GenUpdate_choose state n;
  ret (bits, (S numCalls, state')).

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

Gi_prg_rf: gives the PRF_Adversary the random function oracle and returns what PRF_Adversary returns

PRF_Advantage: defined in terms of PRF_Adversary, indexed by i 
(but PRF_Advantage should be the same for all i) *)

(* Versions of Gen_loop and GenUpdate with that query the oracle in place of (f k) *)
Fixpoint Gen_loop_oc (v : Bvector eta) (n : nat)
  : OracleComp (list bool) (Bvector eta) (list (Bvector eta) * Bvector eta) :=
  match n with
  | O => $ ret (nil, v)
  | S n' =>
    v' <--$ (OC_Query _ (to_list v));
    [bits, v''] <--$2 Gen_loop_oc v' n';
    $ ret (v' :: bits, v'')
  end.

(* takes in key but doesn't use it, to match the type of other GenUpdates *)
Definition GenUpdate_oc (state : KV) (n : nat) :
  OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) :=
  [k, v_0] <-2 state;
  v <--$ (OC_Query _ (to_list v_0));
  [bits, v'] <--$2 Gen_loop_oc v n;
  k' <--$ (OC_Query _ (to_list v' ++ zeroes));
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
(* number of calls starts at 0 and ends at q. say i = 1:
G1:      RB  PRF PRF
Gi_rf 1: RB  RF  PRF
G2:      RB  RB  PRF *)
Definition Oi_oc' (i : nat) (sn : nat * KV) (n : nat) 
  : OracleComp Blist (Bvector eta) (list (Bvector eta) * (nat * KV)) :=
  [numCalls, state] <-2 sn;
  [k, v] <-2 state;
  let GenUpdate_choose := 
      if lt_dec numCalls i (* numCalls < i *)
      then GenUpdate_rb_intermediate_oc
      else if beq_nat numCalls i (* numCalls = i *)
           then GenUpdate_oc    (* uses random function oracle *)
      else if beq_nat numCalls O 
           then GenUpdate_noV_oc  (* first call does not update v *)
      else GenUpdate_PRF_oc in        (* uses PRF with (k,v) updating *)
  [bits, state'] <--$2 GenUpdate_choose (k, v) n;
  $ ret (bits, (S numCalls, state')).

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

Definition PRF_Adversary (i : nat) : OracleComp Blist (Bvector eta) bool :=
  bits <--$ oracleCompMap_outer _ _ (Oi_oc' i) maxCallsAndBlocks;
  $ A bits.

Definition Gi_prg_rf (i : nat) : Comp bool :=
  [b, _] <-$2 PRF_Adversary i _ _ ((randomFunc ({0,1}^eta) _)) nil;
  ret b.

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

  Definition PRF_DRBG_G3 :=
    [b, _] <-$2 PRF_A _ _ (randomFunc ({0,1}^eta) _) nil;
    ret b. *)

Variable eqdbv : EqDec (Bvector eta).
Variable eqdbl : EqDec Blist.

(* TODO: ok to be parametrized by i? *)
Definition PRF_Advantage i : Rat := 
  PRF_Advantage RndK ({0,1}^eta) f eqdbl eqdbv (PRF_Adversary i).

(* should be the same for all i, arbitrarily choose 0 *)
Definition PRF_Advantage_i := PRF_Advantage 0.

(* ----- Unfinished after this *)

Definition Pr_collisions n := n^2 / 2^eta.

(* may need to update this w/ new proof *)
Definition game_bound := PRF_Advantage_i + (Pr_collisions numCalls).

(* base case theorem (adam's) TODO *)

Theorem Gi_Gi_plus_1_close :
  (* TODO: constructed PRF adversary *)
  | Pr[Gi_prg O] - Pr[Gi_prg numCalls] | <= game_bound.
Proof.

Admitted.

(* final theorem *)
Theorem G1_G2_close :
  (* TODO: constructed PRF adversary *)
  (* | Pr[G1_prg] - Pr[G2_prg] | <= (q / 1) * (PRF_Advantage RndK ({0,1}^eta) f _ _ ). *)
  | Pr[G1_prg] - Pr[G2_prg] | <= (numCalls / 1) * game_bound.
Proof.

Admitted.

  (* Notes on our proof:

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
