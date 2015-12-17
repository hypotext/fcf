
Set Implicit Arguments.

Require Import FCF.
(* RndInList has a useful theorem (qam_count) about counting calls to an oracle. *)
Require Import RndInList. 

Section OracleHybrid.

  Variable A B State : Set.
  (* At one point in the proof, we need to know that B is inhabited *)
  Variable b : B. 
  Hypothesis eqdb : EqDec B.
  Hypothesis eqdState : EqDec State.
  
  (* Two oracles, which we want to show are indistinguishable *)
  Variable O1 O2 : State -> A -> Comp (B * State).
  Hypothesis O1_wf : forall s a, well_formed_comp (O1 s a).
  Hypothesis O2_wf : forall s a, well_formed_comp (O2 s a).

  (* The "adversary" that attempts to distinguish the oracles using at most q queries. *)
  Variable A1 : OracleComp A B bool. (* TODO why an oraclecomp? review the setup *)
  (* TODO meaning it takes an oracle of type ^ (and an initial state?), does queries on it, and returns a bool *)
  Hypothesis A1_wf : well_formed_oc A1.
  Variable q : nat.
  Hypothesis A1_qam : queries_at_most A1 q.

  (* We need an initial state for the oracles *)
  Variable s : State.

  (* This proof will show that G1 and G2 are close *)
  Definition G1 := 
    [b, _] <-$2 A1 _ _ O1 s;
    ret b.

  Definition G2 :=
    [b, _] <-$2 A1 _ _ O2 s;
    ret b.

  (* The ith oracle responds to the first (i-1) queries using O1, and the remaining queries using O2. (its state is augmented with a nat for countdown) -- where is the countdown? *)
  Definition Oi (i : nat) (s : (State * nat)) (a : A) : Comp (B * (State * nat)) :=
    [s_s, s_i] <-2 s;           (* just tuple notation *)
    let O_c := if (ge_dec s_i i) then O2 else O1 in
    (* if i < s_i then O1 else O2 *)
    [b, s_s'] <-$2 O_c s_s a;
      ret (b, (s_s', (S s_i))). (* s_i + 1 *)

  (* TODO why does the ith game use the ith oracle? why can't the ith game directly respond to the first (i-1) queries using O1, and the remaining queries using O2?

oh, because it needs to give the oracle to the adversary
i seem to be confused about games vs. oracles, TODO rewrite

How do we go through i games? There's no induction here?

So G1 = G_0 = (Gi q) and G2 = G_q = (Gi 0) *)

  (* TODO could the `q`s differ between games? *)
  (* The ith game uses the ith oracle.  We will show that G1 is the same as (Gi q) and that G2 is the same as (Gi 0).*)
  Definition Gi i :=
    [b, _] <-$2 A1 _ _ (Oi i) (s, 0%nat); (* what's 0 for? oh, the new overall state for Oi is (State * nat), and it increments it on each call *)
    ret b.

  (* We need an assumption that each adjacent pair of games are distant by at most some constant k. *)
  Variable k : Rat.

  (* TODO: this is the (hard) part that we need to show? inductive hypothesis / Update? *)
  Hypothesis Gi_Si_close : 
    forall i,
  | Pr[Gi i] - Pr[Gi (S i)] | <= k. (* G_i and G_{i+1} are close *)


  (* Our proof:

G1: (assume instantiate ideal), then the adversary can query Generate+Update as many times as they want. all are done with PRF.

G2: (assume instantiate ideal), then the adversary can query Generate+Update as many times as they want. all are done with random sampling.

Gi i: (assume instantiate ideal), then the adversary can query Generate+Update as many times as they want (q). the first i calls are done with random sampling, the rest are done normally, with PRF.

Oi: Generate+Update: modified version of PRG that does Generate n + Update with random sampling if < i, and PRF otherwise

G_i_si_close: inductive hypothesis:

given that K and V are randomly sampled (?),
| Pr[G_i] - Pr[G_{i+1}] | <= PRF_advantage + Pr[collisions]
^ more formally, what is PR[collisions]? *)
  

  (* Step 1: show that G1 is the same as (Gi q).  This is actually the most complicated part of this proof. *)

  (* In order to show that G1 is the same as (Gi q), we need an intermediate game that is like G1 except the oracle also keeps track of how many times it was called.  
(TODO: similar to entropy proof?)

We will use an "identical until bad" proof, in which the "bad" event is that the number of queries is greater than q.  The probability of this event is 0, so we end up with an equivalence. *)
  Definition O1_count (s : (State * nat))(a : A) : Comp (B * (State * nat)) :=
    [s_s, s_i] <-2 s;
    [b, s_s'] <-$2 O1 s_s a;
      ret (b, (s_s', (S s_i))).

  Definition G1_count  :=
    [b, s] <-$2 A1 _ _ O1_count (s, 0%nat);
    ret (b, if (gt_dec (snd s) q) then true else false).

  (* We also need a game like Gi that exposes the bad event in the same way as G1_count. Then we can show that G1_count and (Gi_count q) are "identical until bad" and the probability of the "bad" event is 0.  *)
  Definition Gi_count i :=
    [b, s] <-$2 A1 _ _ (Oi i) (s, 0%nat);
    ret (b, if (gt_dec (snd s) q) then true else false).

  Theorem G1_eq_G1_count : 
    Pr[G1] == Pr[x <-$ G1_count; ret (fst x)].

    unfold G1, G1_count.
    fcf_inline_first.
    fcf_to_prhl_eq.
    fcf_skip.
    eapply (fcf_oracle_eq (fun x y => x = fst y)); trivial; intuition; subst.
    unfold O1_count.
    fcf_simp.
    fcf_ident_expand_l.
    fcf_skip.
    fcf_spec_ret; intuition.

    simpl in *; intuition; subst.
    fcf_simp.
    simpl.
    eapply comp_spec_eq_refl.

  Qed.

  Theorem Gi_eq_Gi_count : 
    forall i,
      Pr[Gi i] == Pr[x <-$ Gi_count i; ret (fst x)].
    
    intuition.
    unfold Gi_count, Gi.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    simpl.
    intuition.
  Qed.

  Theorem O1_count_wf :
    forall a b,
    well_formed_comp (O1_count a b).

    intuition.
    unfold O1_count.
    fcf_well_formed.

  Qed.

  Theorem Oi_wf : 
    forall i a b,
      well_formed_comp (Oi i a b).

    intuition.
    unfold Oi.
    fcf_well_formed.
    destruct (ge_dec b0 i); fcf_well_formed.

  Qed.

  (* We will need to know that the count increases by one after each call to O1_count and Oi. *)
  Theorem O1_count_increases : 
    forall d1 b1 c1 a2 b2 c2,
      In (d1, (b1, c1)) (getSupport (O1_count (b2, c2) a2)) ->
      c1 = S c2.

    intuition.
    unfold O1_count in *.
    fcf_simp_in_support.
    destruct x.
    fcf_simp_in_support.
    trivial.
    
  Qed.

  Theorem Oi_count_increases : 
    forall i d1 b1 c1 a2 b2 c2,
      In (d1, (b1, c1)) (getSupport (Oi i (b2, c2) a2)) ->
      c1 = S c2.

    intuition.
    unfold Oi in *.
    fcf_simp_in_support.
    destruct x.
    fcf_simp_in_support.
    trivial.
    
  Qed.

  (* The relational specification on O1_count and (Oi q).  As usual, I arrived at this by attempting some of the theorems below and then factoring out this theorem. *)
  (* TODO simplify this *)
  Theorem O1_count_Oi_eq_until_bad :
    comp_spec 
      (fun a b => 
         ((snd (snd a) > q) <-> (snd (snd b) > q)) 
         /\ ((snd (snd a) <= q)%nat 
             -> (fst a = fst b /\ fst (snd a) = fst (snd b))))
      (A1 _ _ O1_count (s, 0)%nat)
      (A1 _ _ (Oi q) (s, 0)%nat).
    
    eapply comp_spec_consequence.
    eapply (fcf_oracle_eq_until_bad (fun x => if (gt_dec (snd x) q) then true else false) (fun x => if (gt_dec (snd x) q) then true else false) eq); intuition; subst.
    apply O1_count_wf.
    apply Oi_wf.
    pairInv.
    
    unfold O1_count, Oi.
    destruct (ge_dec b1 q).
    fcf_irr_l.
    fcf_irr_r.
    fcf_simp.
    fcf_spec_ret;
      simpl in H2;
      destruct (gt_dec (S b1) q);
      try discriminate;
      try omega.
    
    fcf_skip.
    fcf_spec_ret; intuition.
      
    apply  O1_count_increases in H0.
    simpl in *.
    fcf_compute.

    apply  Oi_count_increases in H0.
    simpl in *.
    fcf_compute.

    intuition; simpl in *.   
    fcf_compute.
    destruct (gt_dec b1 q); trivial.
    destruct (gt_dec (snd (snd b0)) q); intuition; discriminate.
  
    destruct (gt_dec b1 q).
    omega.
    intuition.

    destruct b0.
    destruct (gt_dec b1 q).
    omega.
    intuition.
    simpl in *.
    subst.
    trivial.
    
  Qed.

  Theorem G1_eq_Gi_q : 
    Pr[G1] == Pr[Gi q].

    (* Use the fundamental lemma, where the "bad" event is that the counter in the oracle gets a value > q.  Then use the qam_count theorem from RndInList to show that the probability of this event is 0.  *)

    rewrite G1_eq_G1_count .
    rewrite Gi_eq_Gi_count.

    eapply ratIdentityIndiscernables.
    eapply leRat_impl_eqRat.
    eapply leRat_trans.
    eapply fundamental_lemma_h.

    (* bad events the same*)
    unfold G1_count, Gi_count.
    fcf_inline_first.
    fcf_to_prhl.
    comp_skip.

    apply O1_count_Oi_eq_until_bad.
    simpl in H1.
    intuition; subst.
    fcf_simp.
    simpl in *.
    fcf_spec_ret; fcf_compute.

    (* equal until bad *)
    intuition.
    unfold G1_count, Gi_count.
    fcf_to_prhl.
    comp_skip.
    eapply O1_count_Oi_eq_until_bad.
    simpl in *; intuition.
    fcf_simp.
    destruct p; simpl in *.
    fcf_spec_ret; fcf_compute;
    assert (b1 <= q)%nat by omega; intuition; subst; pairInv; trivial.
  
    (* probability of bad event is 0 *)
    unfold G1_count.
    inline_first.
    fcf_irr_l.
    apply oc_comp_wf; intuition.
    eapply O1_count_wf.

    fcf_simp.
    unfold snd.
    fcf_compute.
    destruct p.
    (* The qam_count theorem takes a function that produces a "count" from the state of the oracle.  This theorem assumes this count increases by at most 1 in each call to the oracle, and that the number of queries is at most q.  Then the result is that the final count is at most q. *)
    eapply (qam_count A1_qam (fun x => snd x)) in H.
    simpl in *.
    omega.
    intuition.
    simpl.    

    apply O1_count_increases in H0.
    omega.
    trivial.

    eapply rat0_le_all.

  Qed.

  (* Step 2: show that G2 is the same as (Gi 0).  This is much simpler. *)
  Theorem G2_eq_Gi_0 : 
    Pr[G2] == Pr[Gi 0%nat].

    unfold G2, Gi.
    fcf_to_prhl_eq.
    comp_skip.
    eapply (fcf_oracle_eq (fun a b => a = fst b)); trivial; intuition; subst.
    unfold Oi.
    comp_simp.
    destruct (ge_dec n 0).
    simpl.
    fcf_ident_expand_l.
    comp_skip.
    eapply comp_spec_ret; intuition.
    omega.

    simpl in  H1.
    intuition; subst.
    comp_simp.
    simpl.
    eapply comp_spec_eq_refl.

  Qed.        

  (* Step 3: rewrite using the equalities in the previous steps, and then use some arithmetic to show that the distance between G1 and G2 is small. *)
  (* TODO no induction here? we gave ourselves the inductive hypothesis, I think *)
  Theorem G1_G2_close : 
    | Pr[G1] - Pr[G2] | <= (q / 1) * k.
                             (* why (q / 1) * k? because we need to cast (q:nat) to Rat *)

    rewrite G1_eq_Gi_q.
    rewrite G2_eq_Gi_0.
    rewrite ratDistance_comm.
    Check distance_le_prod_f.
    (* Print distance_le_prod_f. *)
    (* f is the game;  *)
    Check S.
    Locate distance_le_prod_f.
    (* clear Gi_Si_close. *)
    specialize (distance_le_prod_f (fun i => Pr[Gi i])).
    intuition.
    (* specialize (distance_le_prod_f (fun i => Pr[Gi i])); intuition. *)
  Qed.

End OracleHybrid.