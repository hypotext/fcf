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

(* do not use *)
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
(* TODO convert Gen_loop to use v as (Bvector eta) *)
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

(* final versions *)
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

Definition G1_prg : Comp bool :=
  [k, v] <-$2 Instantiate;
  [bits, _] <-$2 oracleMap _ _ GenUpdate (k, v) maxCallsAndBlocks;
  A bits.

(* TODO: intermediate games with random functions and random bits *)

Definition G2_prg' : Comp bool :=
  [k, v] <-$2 Instantiate;
  [bits, _] <-$2 oracleMap _ _ GenUpdate_rb_oracle tt maxCallsAndBlocks;
  A bits.

Definition G2_prg : Comp bool :=
  [k, v] <-$2 Instantiate;
  bits <-$ compMap _ GenUpdate_rb maxCallsAndBlocks;
  A bits.

Check G1_G2_close.

(* oracle i *)
Definition Oi_prg (i : nat) (sn : nat * KV) (n : nat)
  : Comp (list (Bvector eta) * (nat * KV)) :=
  [numCalls, state] <-2 sn;
  let GenUpdate_choose := if ge_dec numCalls i (* numCalls >= i *)
                          then GenUpdate_rb_intermediate
                          (* first call does not update v, to make proving equiv. easier*)
                          else if beq_nat numCalls O then GenUpdate_noV
                               else GenUpdate in
  (* note: have to use intermediate, not final GenUpdate_rb here *)
  [bits, state'] <-$2 GenUpdate_choose state n;
  ret (bits, (S numCalls, state')).

(* game i (Gi q = G1 and Gi 0 = G2) *)
Definition Gi_prg (i : nat) : Comp bool :=
  [k, v] <-$2 Instantiate;
  [bits, _] <-$2 oracleMap _ _ (Oi_prg i) (O, (k, v)) maxCallsAndBlocks;
  A bits.

(* For PRF adversary *)

(* Working on this. Outline:
(need the types of all of these to fit together)

Gen_loop_oc: takes an oracle in place of (f k)

GenUpdate_oc: takes an oracle in place of (f k)

Oi_prg_rf: if n > i then query GenUpdate_rb, OC version
           else if n = i then query Gen_loop_oc with the given oracle (RF)
           else query GenUpdate, OC version

PRF_Adversary (?): should query the given oracle q times and pass the result to the GenUpdate adversary?
  difficulty: implicit oracle? 

Gi_prg_rf: should give the PRF_Adversary the Oi_prg_rf oracle with the nested random function oracle, and return what PRF_Adversary returns

PRF_Advantage: defined in terms of PRF_Adversary (different type?)
 *)


Fixpoint Gen_loop_oc (v : Bvector eta) (n : nat)
  : OracleComp (list bool) (Bvector eta) (list (Bvector eta) * Bvector eta) :=
  match n with
  | O => $ ret (nil, v)
  | S n' =>
    v' <--$ (OC_Query _ (to_list v));
    [bits, v''] <--$2 Gen_loop_oc v' n';
    $ ret (v' :: bits, v'')
  end.

Definition GenUpdate_oc (v_0 : Bvector eta) (n : nat) :
  OracleComp (list bool) (Bvector eta) (list (Bvector eta) * KV) :=
  v <--$ (OC_Query _ (to_list v_0));
  [bits, v'] <--$2 Gen_loop_oc v n;
  k' <--$ (OC_Query _ (to_list v' ++ zeroes));
  $ ret (bits, (k', v')).

Check GenUpdate.                (* KV -> nat -> Comp (list (Bvector eta) * KV) *)

(* TODO: everything else needs to be converted to GenUpdate_noV's type *)

(* The term "randomFunc ({ 0 , 1 }^eta) eqDecState nil state" has type
 "Comp (Bvector eta * list (KV * Bvector eta))"
 while it is expected to have type
 "KV -> list bool -> Comp (Bvector eta * KV)". *)

Check GenUpdate_oc.
Parameter x : Bvector eta.
Parameter f' : list bool -> Bvector eta.

Hypothesis eqdbl : EqDec Blist.

Check ((randomFunc ({0,1}^eta) eqdbl) nil).
  (* KV -> Comp (Bvector eta * list (KV * Bvector eta)) *)

Hypothesis eqdkv : EqDec KV.

Check GenUpdate_oc x O _ eqdkv.
(* The term "f'" has type "list bool -> Bvector eta"
 while it is expected to have type
 "KV -> list bool -> Comp (Bvector eta * KV)". *)

(* nested oracles *)
(* Definition Oi_prg_rf (i : nat) (sn : nat * KV) (n : nat) *)
(*   : Comp (list (Bvector eta) * (nat * KV)) := *)
(*   [numCalls, state] <-2 sn; *)
(*   [k, v] <-2 state; *)
(*   let GenUpdate_choose := (* if ge_dec numCalls i *) *)
(*                           (* then GenUpdate_rb_intermediate *) *)
(*                           (* (* first call does not update v, to make proving equiv. easier*) *) *)
(*                           (* else if beq_nat i numCalls then GenUpdate_oc *) *)
(*                           (* else if beq_nat i O then GenUpdate_noV *) *)
(*                           (*      else GenUpdate in *) *)
(*       GenUpdate_oc in *)
(*   (* note: have to use intermediate, not final GenUpdate_rb here *) *)
(*   [bits, state'] <-$2 GenUpdate_choose v n _ _ ((randomFunc ({0,1}^eta) _) nil); *)
(*     (* one oracle is randomFunc, one is F *) *)
(*   ret (bits, (S numCalls, state')). *)

Parameter Oi_prg_rf : nat -> nat * KV -> nat -> Comp (list (Bvector eta) * (nat * KV)).

(* f : Bvector eta -> Blist -> Bvector eta *)
(* this should get the result (passing in o) and return the result of the GenUpdate oracle *)
(* Definition PRF_Adversary : OracleComp Blist (Bvector eta) bool := *)
   (* [bits, _] <-2 oracleMap ... given oracle (opaque initial state?) maxCallsAndBlocks  *)
   (* A bits. (this is a game, though?) *)

    (* ls <--$ PRF_DRBG_f_G2 v_init l; *)
    (* $ A ls.  *)
Parameter PRF_Adversary : OracleComp Blist (Bvector eta) bool.
(* the type will be different given that we're giving it Oi_prg, not f_oracle *)
(* confused: there has to be a RF oracle slot for GenUpdate_oc, but there also has to be (k,v) for the GenUpdate oracle -- unless that is (f k)? *)

Definition Gi_prg_rf (i : nat) : Comp bool :=
    (* we should give PRF_A the (Oi_prg i) that has been given the random function oracle *)
  (* [k, v] <-$2 Instantiate; *)
  (* [bits, _] <-$2 oracleMap _ _ (Oi_prg i) (O, (k, v)) maxCallsAndBlocks; *)
  (* A bits. *)
  (* OracleComp should take care of PRF_adversary not being able to see (O, (k, v)) *)
    [b, _] <-$2 PRF_Adversary _ _ (Oi_prg i ((randomFunc ({0,1}^eta) _) nil) (O, (k, v));
    ret b.

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

Definition PRF_Advantage_ : Rat := PRF_Advantage RndK ({0,1}^eta) f _ _ PRF_Adversary.

Definition Pr_collisions n := n^2 / 2^eta.

(* may need to update this w/ new proof *)
Definition game_bound := PRF_Advantage_ + (Pr_collisions numCalls).

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
