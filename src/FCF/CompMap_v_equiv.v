
Set Implicit Arguments.

Require Import FCF.
Require Import CompFold.
Require Import HasDups.

Section Temp.

Variable eta : nat.

Definition compMap_v (ls : list nat) (v : Bvector eta) :=
  x <-$ compMap _ (fun _ => {0,1}^eta) ls;
  ret hasDups _ (v :: x).

Theorem compMap_v_eq_h:
  forall ls lsb  (a b : Bvector eta), 
    ~In a lsb ->
    ~In b lsb ->
    comp_spec eq 
  (x <-$
      compMap (Bvector_EqDec eta) (fun _ : nat => { 0 , 1 }^ eta) ls;
      ret hasDups (Bvector_EqDec eta) (a :: lsb ++ x))
  (x <-$
      compMap (Bvector_EqDec eta) (fun _ : nat => { 0 , 1 }^ eta) ls;
      ret hasDups (Bvector_EqDec eta) (b :: lsb ++ x)).


  induction ls; intuition; simpl in *; fcf_simp.
  repeat rewrite app_nil_r.
  destruct ( in_dec (EqDec_dec (Bvector_EqDec eta)) a lsb);
  destruct (in_dec (EqDec_dec (Bvector_EqDec eta)) b lsb); 
  try reflexivity; try congruence.

  fcf_inline_first.
  eapply comp_spec_seq; eauto with inhabited.

  eapply (comp_spec_iso (fun x => if (eqb a0 x) then b else if (eqb b x) then a0 else x) (fun x => if (eqb a0 x) then b else if (eqb b x) then a0 else x)); intuition.
  
  (* forward direction *)
  case_eq (eqb b x); intuition.
  rewrite eqb_leibniz in H2; subst.

  case_eq (eqb a0 x); intuition.
  rewrite H2.
  trivial.
  rewrite eqb_refl.
  trivial.

  rewrite eqb_false_iff in H2.

  case_eq (eqb a0 x); intuition.
  rewrite eqb_leibniz in H3.
  subst.

  case_eq (eqb x b); intuition.
  rewrite eqb_leibniz in H3.
  intuition.

  rewrite eqb_refl.
  trivial.

  rewrite H3.
  eapply eqb_false_iff in H2.
  rewrite H2.
  trivial.
  
  (* backward direction *)
  
  case_eq (eqb a0 x); intuition.
  rewrite eqb_leibniz in H2. subst.
  case_eq (eqb x b); intuition.
  rewrite eqb_leibniz in H2.
  intuition.

  rewrite eqb_refl.
  trivial.

  eapply eqb_false_iff in H2.
  case_eq (eqb b x); intuition.

  rewrite eqb_refl.
  eapply eqb_leibniz; intuition.

  rewrite H3.
  case_eq (eqb a0 x); intuition.
  rewrite eqb_leibniz in H4.
  congruence.

  (* range of function is correct *)
  simpl.
  apply in_getAllBvectors.

  (* probability is unchanged---follows form uniformity *)
  eapply comp_spec_rnd.

  (* Now use the postcondition to complete the proof *)
  intuition.

  case_eq (a0 ?= a1); intuition.
  rewrite H4 in H3.
  rewrite eqb_leibniz in H4.
  subst.
  fcf_inline_first.
  fcf_skip.
  fcf_simp.
  eapply comp_spec_ret.
  destruct (in_dec (EqDec_dec (Bvector_EqDec eta)) a1 (lsb ++ a1 :: b)).
  destruct (in_dec (EqDec_dec (Bvector_EqDec eta)) b0 (lsb ++ b0 :: b)); trivial.
  exfalso.
  eapply n.
  eapply in_or_app.
  right.
  simpl.
  intuition.
  exfalso.
  eapply n.
  eapply in_or_app.
  right.
  simpl.
  intuition.

  rewrite H4 in H3.
  case_eq (b ?= a1); intuition.
  rewrite eqb_leibniz in H5.
  subst.
  rewrite eqb_refl.
  fcf_inline_first.
  fcf_skip.
  fcf_simp.
  eapply comp_spec_ret.
  assert (a0 <> a1).
  eapply eqb_false_iff; intuition.
  destruct ( in_dec (EqDec_dec (Bvector_EqDec eta)) a0 (lsb ++ a1 :: b)).
  eapply in_app_or in i.
  intuition.
  simpl in *.
  intuition; subst.
  intuition.
  assert (hasDups (Bvector_EqDec eta) (lsb ++ a0 :: b) = true).
  eapply hasDups_true_not_NoDup.
  intuition.
  eapply NoDup_app in H7.
  intuition.  
  inversion H7; subst; clear H7.
  intuition.
  rewrite H7.
  destruct (in_dec (EqDec_dec (Bvector_EqDec eta)) a1 (lsb ++ a0 :: b)); trivial.
  destruct (in_dec (EqDec_dec (Bvector_EqDec eta)) a1 (lsb ++ a0 :: b)).
  eapply in_app_or in i.
  intuition.
  simpl in *.
  intuition.
  eapply hasDups_true_not_NoDup.
  intuition.
  eapply NoDup_app in H7.
  intuition.
  inversion H7; subst; clear H7.
  intuition.

  case_eq (hasDups (Bvector_EqDec eta) (lsb ++ a1 :: b)); intuition.
  apply hasDups_true_not_NoDup in H7.
  case_eq (hasDups (Bvector_EqDec eta) (lsb ++ a0 :: b)); intuition.
  apply hasDups_false_NoDup in H8.
  exfalso.
  eapply H7.
  eapply NoDup_app in H8.
  intuition.
  inversion H8; subst; clear H8.
  eapply app_NoDup; intuition.
  econstructor.
  intuition.
  intuition.
  simpl in *.
  intuition. subst.
  intuition.
  eapply H11.
  eapply H8.
  right.
  eapply H12.
  trivial.
  simpl in *. intuition; subst; intuition.
  eapply H11.
  eapply H10.
  right.
  eapply H12.
  trivial.

  apply hasDups_false_NoDup in H7.
  case_eq (hasDups (Bvector_EqDec eta) (lsb ++ a0 :: b)); intuition.
  eapply hasDups_true_not_NoDup in H8.
  exfalso.
  eapply H8.
  eapply NoDup_app in H7.
  intuition.
  inversion H7; subst; clear H7.
  eapply app_NoDup; intuition.
  econstructor.
  intuition.
  intuition.
  simpl in *.
  intuition. subst.
  intuition.
  eapply H11.
  eapply H7.
  right.
  eapply H12.
  trivial.
  simpl in *. intuition; subst; intuition.
  eapply H11.
  eapply H10.
  right.
  eapply H12.
  trivial. 
 
  (* 1 left *)

  rewrite H5 in H3.
  subst.
  assert (forall lsb a0 a1, comp_spec eq (x <-$
      (lsb' <-$
       compMap (Bvector_EqDec eta) (fun _ : nat => { 0 , 1 }^ eta) ls;
       ret (a1 :: lsb')%list);
      ret (if in_dec (EqDec_dec (Bvector_EqDec eta)) a0 (lsb ++ x)
           then true
           else hasDups (Bvector_EqDec eta) (lsb ++ x)))  
          (x <-$
      (compMap (Bvector_EqDec eta) (fun _ : nat => { 0 , 1 }^ eta) ls);
      ret (if in_dec (EqDec_dec (Bvector_EqDec eta)) a0 ((lsb ++ (a1 :: nil)) ++ x)
           then true
           else hasDups (Bvector_EqDec eta) ((lsb ++ (a1 ::nil)) ++  x)))).
  intuition.
  fcf_inline_first.
  fcf_skip.
  rewrite app_cons_eq.
  reflexivity.

  rewrite H3.
  rewrite H3.

  eapply IHls.

  intuition.
  eapply in_app_or in H6.
  intuition.
  simpl in *; intuition; subst; intuition.
  rewrite eqbBvector_complete in H4.
  discriminate.

  intuition.
  eapply in_app_or in H6.
  intuition.
  simpl in *; intuition; subst; intuition.
  rewrite eqbBvector_complete in H5.
  discriminate.
  
Qed.


Theorem compMap_v_eq:
  forall ls (a b : Bvector eta), 
    comp_spec eq (compMap_v ls a) (compMap_v ls b).

  intuition.
  unfold compMap_v.
  eapply (compMap_v_eq_h ls nil); intuition.

Qed.

End Temp.