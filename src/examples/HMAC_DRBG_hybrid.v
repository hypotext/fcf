Set Implicit Arguments.

Require Import FCF.
(* RndInList has a useful theorem (qam_count) about counting calls to an oracle. *)
Require Import RndInList. 
Require Import HasDups.
Require Import CompFold.
Require Import PRF.

  (* TODO:
What's the simplest and best way to incrementally build this up, combining both proofs?

- Blist definitions X
- New for PRF-DRBG etc functions (instantiate, generate, update) X
- Make the correct oracles X
- Fill in the oracles with functions X

- Write the initial game and final game X
- Write the game i X
- Write the theorem statements (final theorem, inductive hypothesis)

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
   note: the key type is now also Bvector eta, since HMAC specifies that the key has the same size as the output (simplified) *)
Variable eta : nat.

Variable RndK : Comp (Bvector eta).
Variable RndV : Comp Blist.

Variable f : Bvector eta -> Blist -> Bvector eta.

Definition KV : Set := (Bvector eta * Blist)%type.
Hypothesis eqDecState : EqDec KV.

(* injection is Vector.to_list. TODO prove this *)
Variable injD : Bvector eta -> Blist.
Hypothesis injD_correct :
  forall r1 r2, injD r1 = injD r2 -> r1 = r2.

(* PRG functions *)

(* instantiate *)
Definition Instantiate : Comp KV :=
  k <-$ RndK;
  v <-$ RndV;
  ret (k, v).

(* save the last v and output it *)
Fixpoint PRF_DRBG (k : Bvector eta) (v : Blist) (n : nat) : list (Bvector eta) * Blist :=
  match n with
  | O => (nil, v)
  | S n' =>
    let v' := f k v in
    let (bits, v'') := PRF_DRBG k (Vector.to_list v') n' in
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

Definition GenUpdate (state : KV) (n : nat) :
  Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  [bits, v'] <-2 PRF_DRBG k v n;
  k' <- f k (v' ++ zeroes);
  v'' <- f k' v';
  ret (bits, (k', Vector.to_list v'')).

(* oracle 2: all PRFs replaced with random bits *)
(* TODO: intermediate oracles, each with random functions *)

Fixpoint PRF_DRBG_rb (k : Bvector eta) (v : Blist) (n : nat)
  : Comp (list (Bvector eta) * Blist) :=
  match n with
  | O => ret (nil, v)
  | S n' =>
    v' <-$ {0,1}^eta;
    [bits, v''] <-$2 PRF_DRBG_rb k (Vector.to_list v') n';
    ret (v' :: bits, v'')
  end.

Definition GenUpdate_rb (state : KV) (n : nat) 
  : Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  [bits, v'] <-2 PRF_DRBG k v n;
  k' <-$ {0,1}^eta;
  v'' <-$ {0,1}^eta;
  ret (bits, (k', Vector.to_list v'')).

(* TODO: prove well_formed for the oracles *)

Variable A : OracleComp nat (list (Bvector eta)) bool.
Hypothesis A_wf : well_formed_oc A.

Variable q : nat.
Hypothesis A_qam : queries_at_most A q.

(* don't forget instantiate, which creates the initial state *)
Definition G1_prg : Comp bool :=
  [k, v] <-$2 Instantiate;    (* does not model external entropy *)
  [b, _] <-$2 A _ _ GenUpdate (k, v);
  ret b.

(* TODO: intermediate games with RF and RB *)

Definition G2_prg : Comp bool :=
  [k, v] <-$2 Instantiate;
  [b, _] <-$2 A _ _ GenUpdate_rb (k, v);
  ret b.

(* oracle i *)

Definition Oi_prg (i : nat) (sn : nat * KV) (n : nat)
  : Comp (list (Bvector eta) * (nat * KV)) :=
  [numCalls, state] <-2 sn;
  let GenUpdate_choose := if ge_dec numCalls i then GenUpdate_rb else GenUpdate in
  [bits, state'] <-$2 GenUpdate_choose state n;
  ret (bits, (S numCalls, state')).

Definition Gi_prg (i : nat) : Comp bool :=
  [k, v] <-$2 Instantiate;
  [b, _] <-$2 A _ _ (Oi_prg i) (O, (k, v));
  ret b.

(* base case (adam's) TODO *)

(* inductive case (with inductive hypothesis) TODO *)

(* final theorem *)
Check PRF_Advantage.

(* Should it be against GenUpdate or PRF_DRBG? breaking either implies breaking the PRF
i guess we just use the adversary we have already 
also, the PRF_A shows up in almost every subsequent game *)

(* (f k, v) instead of (k, v) *)
Definition State := ((Blist -> Bvector eta) * Blist)%type.

(* TODO: change these to use new State *)
Fixpoint PRF_DRBG_oc (k : Bvector eta) (v : Blist) (n : nat) : list (Bvector eta) * Blist :=
  match n with
  | O => (nil, v)
  | S n' =>
    let v' := f k v in
    let (bits, v'') := PRF_DRBG k (Vector.to_list v') n' in
    (v' :: bits, v'')
  end.

Definition GenUpdate_oc (state : KV) (n : nat) :
  Comp (list (Bvector eta) * KV) :=
  [k, v] <-2 state;
  [bits, v'] <-2 PRF_DRBG k v n;
  k' <- f k (v' ++ zeroes);
  v'' <- f k' v';
  ret (bits, (k', Vector.to_list v'')).

Parameter GenUpdate_oc' :
  State -> nat -> OracleComp Blist (Bvector eta) (list (Bvector eta) * State).

Check A.                        (* OracleComp nat (list (Bvector eta)) bool *)
Check OC_Run.
Parameter init : KV.
Print OracleComp.
Parameter k : Bvector eta.
Parameter v : Blist.

Hypothesis eds : EqDec State.

  (* [k, v] <-$2 Instantiate;      (* is this right? no, key instantiated in game *) *)

(* intuitively, what I want is to give PRF_Adversary an oracle (f k). It will plug it into GenUpdate that uses that oracle, then give the resulting function to the GenUpdate adversary A, and return what it outputs.

PRF_A should not be able to see or choose the key. Can it see or choose the v?

The problem is that using OC_Run requires the PRF_Adv to give and get the GenUpdate state, since that's an oracle computation? *)

Definition PRF_Adversary : OracleComp Blist (Bvector eta) bool :=
  (* but if i make GenUpdate an OracleComp, then A won't accept it? *)
  (* how to NOT give it access to the initial key? *)
  (* v <--$ RndV; (* can't seem to mix Comp and OracleComp. should it be able to see v? choose v? *) *)
  (* can I name the input oracle that is "f k" and pass it in here? *)
  [b, _] <--$2 OC_Run _ _ _ A GenUpdate_oc' (f k, v);
  (* theoretically here the PRF_adversary would have access to the final (updated) key.
   would that matter? *)
  (* should I modify GenUpdate_oc to not take the key as state in/out? *)
  $ (ret b).

Definition PRF_Advantage_ : Rat := PRF_Advantage RndK ({0,1}^eta) f _ _ PRF_Adversary.

Definition Pr_collisions n := n^2 / 2^eta.

Definition game_bound := (2/1) * PRF_Advantage_ + (Pr_collisions q).

Theorem Gi_Gi_plus_1_close :
  (* TODO: constructed PRF adversary *)
  | Pr[Gi_prg O] - Pr[Gi_prg q] | <= game_bound.
Proof.

Admitted.

(* final theorem *)
Theorem G1_G2_close :
  (* TODO: constructed PRF adversary *)
  (* | Pr[G1_prg] - Pr[G2_prg] | <= (q / 1) * (PRF_Advantage RndK ({0,1}^eta) f _ _ ). *)
  | Pr[G1_prg] - Pr[G2_prg] | <= (q / 1) * game_bound.
Proof.

Admitted.

  (* Notes on our proof:

G1: (assume instantiate ideal), then the adversary can query Generate+Update as many times as they want. all are done with PRF.

G2: (assume instantiate ideal), then the adversary can query Generate+Update as many times as they want. all are done with random sampling.

Gi i: (assume instantiate ideal), then the adversary can query Generate+Update as many times as they want (q). the first i calls are done with random sampling, the rest are done normally, with PRF.

Gi_0: the game as-is (PRF)

Gi_1: replace PRF updating K with a random function first 

** here: should the oracle keep track of all calls to the RF over all calls to GenUpdate?

Gi_2: replace RF updating K with randomly-sampled bits

Gi_3: replace PRF updating K with a random function first 

Gi_4: replace RF updating K with randomly-sampled bits
  (Gi_3 and 4: done instead of replacing the PRF for both K and V at the same time.
   the result will have an extra q * PRF_Advantage in the final bound)

---

Oi: Generate+Update: modified version of PRG that does Generate n + Update with random sampling if < i, and PRF otherwise

G_i_si_close: inductive hypothesis:

given that K and V are randomly sampled,
| Pr[G_i] - Pr[G_{i+1}] | <= PRF_advantage + Pr[collisions]
              or is it <= 2 * (PRF_advantage + Pr[collisions]) ?
              or <= 2 * PRF_advantage + Pr[collisions] ?

Pr[collisions] = 
"probability that /given the maximum input size n to any call/, the RF will be called on two identical inputs within the same oracle call"

the RF used both within the Generate loop and outside to generate the key?
but K <- RF(K, V || 0x00) so there can't be any collision within this call?

in the previous call, we have 
V_{n+1} <- RF(K_n, V_n)

Generate for x blocks:
V_{n+1} through V_{n+1 + x} <-- each one is random

then
K_{n+1} <- RF(K_n, V_{n+1 + x} || 0x00)

so we aren't using the list tactic anymore

but also the induction hypothesis that K and V have been randomly sampled
-- maybe we can change it?
since we aren't dealing with anything in the previous call at the random function level
unless we aggregate all of them into a list?

pr[collisions] is a function of the number of times RF1 was called, which is n+1
(can we still find pr[collisions] using the list way?)
does pr[collisions] rely on the inductive hypothesis?

how would i have redesigned the protocol with proof in mind?
would resampling v, then K, have worked?

why do we need the induction hypothesis in the current version? (that k, v are randomly sampled) if all the v's are randomly sampled, then the output is random

are we dealing with global collisions b/t the randomly sampled k and v?

can we re-use matt's computational argument and move the re-sampling of v to the top?
change the inductive hypothesis to just that K has been randomly sampled and the un-updated v has been randomly sampled

then we can prove it again?

unsure how to deal with n+1 in fcf, but also unsure how to make the computational argument w/ inlining programs 

 *)
