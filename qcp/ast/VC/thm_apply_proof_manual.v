Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import thm_apply_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
From MonadLib.StateRelMonad Require Import StateRelMonad StateRelBasic StateRelHoare FixpointLib safeexec_lib.
Import naive_C_Rules.
From SimpleC.EE Require Import ast_lib.
From SimpleC.EE Require Import malloc.
From SimpleC.EE Require Import sll_tmpl.
Import naive_C_Rules.
Local Open Scope sac.

Lemma sllbseg_seg: forall x y z l1 l2,
  sllbseg_term_list x y l1 **
  sllbseg_term_list y z l2 |--
  sllbseg_term_list x z (l1++l2).
Proof.
  intros.
  revert x; induction l1; simpl; intros.
  + entailer!.
  subst x.
  entailer!.
  + Intros u.
  Exists u.
  entailer!.
Qed.

Lemma sllbseg_one_app: forall a l x y z retval,
  retval <> NULL ->
  sllbseg_term_list x y l **
  y # Ptr |-> retval **
  &(retval # "term_list" ->ₛ "element") # Ptr |-> z **
  store_term z a |--
  sllbseg_term_list x &(retval # "term_list" ->ₛ "next") (l++(a::nil)).
Proof.
  intros.
  sep_apply (store_term_cell_fold retval z a); [ | auto].
  sep_apply sllbseg_one; [ | auto].
  sep_apply (sllbseg_seg x y &( retval # "term_list" ->ₛ "next") l (a :: nil)).
  entailer!.
Qed.

Lemma proof_of_sub_thm_return_wit_1 : sub_thm_return_wit_1.
Proof.
  pre_process.
  rewrite H.
  unfold sll_var_sub_list.
  pose proof (sll_zero store_var_sub_cell "var_sub_list" "next" 0 l).
  unfold NULL in H0.
  assert (0=0). {reflexivity. }
  pose proof H0 H1.
  destruct l.
  + entailer!. 
    unfold store_sub_thm_res.
    pose proof thm_subst_nil t; rewrite H3.
    unfold store_partial_quant.
    entailer!.
  + apply sll_zero_right; discriminate.
Qed.

Lemma proof_of_sub_thm_return_wit_2 : sub_thm_return_wit_2.
Proof.
  pre_process.
  unfold sll_var_sub_list.
  rewrite H6, H2.
  pose proof (sll_var_sub_list_fold lis_pre lis_cur l0 sy sz sv st lis_next H7 H1).
  sep_apply H8.
  unfold sll_var_sub_list.
  entailer!.
  sep_apply store_sub_thm_res_fold; [ | auto].
  rewrite H3; entailer!.
Qed.

Lemma proof_of_sub_thm_return_wit_3 : sub_thm_return_wit_3.
Proof. 
  pre_process.
  unfold sll_var_sub_list, store_var_sub.
  destruct vs.
  Intros y z.
  sep_apply sll_var_sub_list_fold; [ | auto | auto ].
  unfold sll_var_sub_list; rewrite <- H1; entailer!.
  unfold store_sub_thm_res.
  destruct t.
  + pose proof thm_subst_allres_var var (VarSub name t0) l0.
    rewrite <- H1 in H6; rewrite H6.
    pose proof thm_subst'_var var (VarSub name t0) l0.
    rewrite <- H1 in H7; rewrite H7.
    unfold store_term, store_term'.
    Intros x; Exists x.
    entailer!.
  + pose proof thm_subst_allres_const ctype content (VarSub name t0) l0.
    rewrite <- H1 in H6; rewrite H6.
    pose proof thm_subst'_const ctype content (VarSub name t0) l0.
    rewrite <- H1 in H7; rewrite H7.
    unfold store_term, store_term'.
    entailer!.
  + pose proof thm_subst_allres_apply t1 t2 (VarSub name t0) l0.
    rewrite <- H1 in H6; rewrite H6.
    pose proof thm_subst'_apply t1 t2 (VarSub name t0) l0.
    rewrite <- H1 in H7; rewrite H7.
    unfold store_term, store_term'.
    fold store_term.
    Intros x sy; Exists x sy.
    entailer!.
  + unfold termtypeID in H; congruence.
Qed.

Lemma proof_of_sub_thm_partial_solve_wit_3_pure : sub_thm_partial_solve_wit_3_pure.
Proof.
  pre_process.
  sep_apply store_term_unfold.
  sep_apply store_term_unfold.
  unfold store_string.
  Intros n1 n2.
  entailer!.
Qed.

Lemma proof_of_sub_thm_which_implies_wit_1 : sub_thm_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply store_term_unfold.
  pose proof sll_not_zero store_var_sub_cell "var_sub_list" "next" lis l H.
  unfold sll_var_sub_list.
  sep_apply H0.
  unfold store_var_sub_cell at 1.
  Intros y a l0 y0.
  Exists y y0 a l0.
  entailer!.
Qed.

Lemma proof_of_sub_thm_which_implies_wit_2 : sub_thm_which_implies_wit_2.
Proof.
  pre_process.
  sep_apply store_term'_Quant; [ | auto | auto ].
  Intros qtype qvar body y z.
  destruct vs.
  unfold store_var_sub.
  Intros sy sz.
  Exists sz sy z y name.
  Exists t0 qtype qvar body.
  entailer!.
Qed.

Lemma proof_of_separate_imply_return_wit_1 : separate_imply_return_wit_1.
Proof.
  pre_process.
  unfold store_imply_res.
  unfold sep_impl.
  destruct trm; unfold NULL in *.
  - sep_apply (store_term_fold_out t_pre (TermVar var)).
    entailer!.
    entailer!.
  - sep_apply store_term_fold_out.
    entailer!.
    entailer!.
  - contradiction.
  - sep_apply store_term_fold_out.
    entailer!.
    entailer!.
Qed.

Lemma proof_of_separate_imply_return_wit_2 : separate_imply_return_wit_2.
Proof.
  pre_process.
  rewrite H1.
  unfold store_term at 2.
  fold store_term.
  Exists v_2 v.
  entailer!.
  sep_apply store_term_fold_out.
  entailer!.

  unfold store_imply_res.
  unfold sep_impl.
  destruct lt.

  - entailer!.
  - entailer!.
  - contradiction.
  - entailer!.
  - lia.
Qed.

Lemma proof_of_separate_imply_return_wit_3 : separate_imply_return_wit_3.
Proof.
  pre_process.
  rewrite H4.
  unfold store_term at 3.
  fold store_term.
  rewrite H1.
  unfold store_term at 3.
  fold store_term.
  Exists v_2 v v_4 v_3.

  sep_apply ((store_term_fold_out v_4 ll) H0).
  entailer!.

  unfold store_imply_res.
  unfold sep_impl.
  destruct ll.
  - entailer!.
  - contradiction.
  - entailer!.
  - entailer!.
Qed.

Lemma proof_of_separate_imply_return_wit_4 : separate_imply_return_wit_4.
Proof.
  pre_process.
  rewrite H6.
  unfold store_term at 3.
  fold store_term.
  Exists v_2 v.
  entailer!.

  rewrite H3.
  unfold store_term at 2.
  fold store_term.
  Exists v_4 v_3.
  entailer!.

  rewrite H0.
  unfold store_term.
  entailer!.

  unfold store_imply_res.
  unfold sep_impl.
  destruct llctype.
  - entailer!.
  - entailer!.
  - entailer!.
  - entailer!.
  - entailer!.
  - entailer!.
  - entailer!.
  - contradiction.
Qed. 

Lemma proof_of_separate_imply_return_wit_5 : separate_imply_return_wit_5.
Proof.
  pre_process.
  unfold store_imply_res.
  unfold sep_impl.
  rewrite H6.
  rewrite H3.
  rewrite H0.
  unfold ctID in H.
  destruct llctype; try lia.
  Exists t1' t2'.
  unfold store_term.
  fold store_term.
  Exists v_2 v.
  Exists v_4 v_3.
  entailer!.
Qed.

Lemma proof_of_separate_imply_which_implies_wit_1 : separate_imply_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply store_term_unfold.
  unfold NULL.
  entailer!.
Qed.

Lemma proof_of_separate_imply_which_implies_wit_2 : separate_imply_which_implies_wit_2.
Proof.
  pre_process.
  sep_apply store_term'_Apply; unfold NULL in *.
  Intros lt rt y z.
  Exists z y lt rt.
  rewrite H3.
  entailer!.
  lia.
  lia.
Qed.

Lemma proof_of_separate_imply_which_implies_wit_3 : separate_imply_which_implies_wit_3.
Proof.
  pre_process.
  sep_apply store_term_unfold.
  unfold NULL.
  entailer!.
Qed.

Lemma proof_of_separate_imply_which_implies_wit_4 : separate_imply_which_implies_wit_4.
Proof.
  pre_process.
  sep_apply store_term'_Apply; unfold NULL in *.
  Intros ll lr y z.
  Exists z y ll lr.
  entailer!.
  lia.
  lia.
Qed. 

Lemma proof_of_separate_imply_which_implies_wit_5 : separate_imply_which_implies_wit_5.
Proof.
  pre_process.
  sep_apply store_term_unfold.
  unfold NULL.
  entailer!.
Qed.

Lemma proof_of_separate_imply_which_implies_wit_6 : separate_imply_which_implies_wit_6.
Proof.
  pre_process.
  sep_apply store_term'_Const; unfold NULL in *.
  Intros ty ct.
  Exists ty ct.
  rewrite <- H3.
  entailer!.
  lia.
  lia.
Qed. 

Lemma proof_of_check_list_gen_entail_wit_1 : check_list_gen_entail_wit_1.
Proof.
  pre_process.
  Exists theo nil.
  entailer!.
  unfold sllbseg_term_list, sllbseg.
  entailer!.
Qed.

Lemma proof_of_check_list_gen_entail_wit_2 : check_list_gen_entail_wit_2.
Proof.
  pre_process.
  Exists tr (l_2 ++ (r::nil)).
  entailer!.
  + sep_apply sllbseg_one_app; [ entailer! | auto].
  + subst.
    clear - H4 H3.
    unfold check_from_mid_rel in *.
    rewrite (repeat_break_unfold _ _) in H4.
    prove_by_one_abs_step (by_continue (tr, targ, l_2 ++ r :: nil)).
    unfold check_list_gen_body.
    unfold term_alpha_eqn in H3.
    destruct term_alpha_eq; [ lia | ].
    unfold sep_impl.
    abs_ret_step.
Qed.

Lemma proof_of_check_list_gen_return_wit_1 : check_list_gen_return_wit_1.
Proof.
  pre_process.
  subst.
  sep_apply store_imply_res_zero.
  Exists t_2 nil.
  simpl; entailer!.
  unfold check_from_mid_rel in *.
  rewrite (repeat_break_unfold _ _) in H2.
  prove_by_one_abs_step (by_break (makepair t_2 nil)).
  unfold check_list_gen_body.
  unfold term_alpha_eqn in H1.
  destruct term_alpha_eq eqn:Heq; [ congruence | ].
  rewrite H.
  abs_ret_step.
Qed.

Lemma proof_of_check_list_gen_return_wit_2 : check_list_gen_return_wit_2.
Proof.
  pre_process.
  Exists t_2 l_2.
  entailer!.
  unfold check_from_mid_rel in *.
  rewrite (repeat_break_unfold _ _) in H1.
  prove_by_one_abs_step (by_break (makepair t_2 l_2)).
  unfold check_list_gen_body.
  unfold term_alpha_eqn in H0.
  destruct term_alpha_eq eqn:Heq; [ | congruence].
  abs_ret_step.
Qed.

Lemma proof_of_check_list_gen_which_implies_wit_1 : check_list_gen_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply sllbseg_2_sllseg_term.
  Intros c; Exists c; entailer!.
Qed.

Lemma proof_of_check_list_gen_which_implies_wit_2 : check_list_gen_which_implies_wit_2.
Proof.
  pre_process.
  unfold store_imply_res.
  destruct (sep_impl ttm) eqn:Heq; [ | entailer!].
  destruct i.
  Intros y z.
  unfold sep_impl in Heq.
  destruct ttm eqn:Heq1; try congruence.
  destruct t1 eqn:Heq11; try congruence.
  destruct t3 eqn:Heq111; try congruence.
  destruct ctype eqn:Hc; try congruence.
  unfold store_ImplyProp.
  Exists z y content t4 t2.
  inversion Heq.
  entailer!.
Qed.

Lemma proof_of_check_list_gen_which_implies_wit_3 : check_list_gen_which_implies_wit_3.
Proof.
  pre_process.
  unfold store_ImplyProp.
  entailer!.
Qed.

Lemma proof_of_check_list_gen_which_implies_wit_4 : check_list_gen_which_implies_wit_4.
Proof.
  pre_process.
  sep_apply sllbseg_2_sllseg_term.
  Intros c; Exists c; entailer!.
Qed.

Lemma partial_quant_combine: forall t l pq st retval thm_pre,
  thm_pre <> 0 ->
  thm_subst_allres t l = Some (pq, st) ->
      store_term retval st ** store_partial_quant thm_pre retval pq
      |-- store_term thm_pre (thm_subst' t l).
Proof.
  intros. revert H H0. revert t l pq st thm_pre.
  induction t.
  + intros.
    unfold thm_subst_allres in H0.
    destruct l.
  - inversion H0; subst.
    unfold store_partial_quant.
    entailer!.
    rewrite H1.
    entailer!.
  - destruct v; congruence.
  + intros. 
    unfold thm_subst_allres in H0.
    destruct l.
  - inversion H0; subst.
    unfold store_partial_quant.
    entailer!.
    rewrite H1.
    entailer!.
  - destruct v; congruence.
  + intros. 
    unfold thm_subst_allres in H0.
    destruct l.
  - inversion H0; subst.
    unfold store_partial_quant.
    entailer!.
    rewrite H1.
    entailer!.
  - destruct v; congruence.
  + intros.
    unfold thm_subst_allres in H0.
    destruct l.
  - inversion H0; subst.
    unfold store_partial_quant.
    entailer!.
    rewrite H1.
    entailer!.
  - destruct v.
    unfold thm_subst'; fold thm_subst'.
    fold thm_subst_allres in H0.
    destruct (thm_subst_allres (term_subst_t t0 name t) l) eqn:Heq; [ | congruence].
    destruct p.
    inversion H0; subst.
    unfold store_partial_quant; fold store_partial_quant.
    unfold store_term at 2; fold store_term.
    unfold termtypeID.
    Intros y z; Exists y z.
    entailer!.
    unfold thm_subst_allres in Heq.
Admitted.

Lemma proof_of_thm_apply_return_wit_1_1 : thm_apply_return_wit_1_1.
Proof. 
  pre_process.
  Exists (thm_subst' t_3 l) (SRTList l_2).
  unfold thm_subst_allres_rel in H5.
  unfold store_solve_res.
  Exists retval_2.
  unfold restypeID.
  entailer!.
  + sep_apply (partial_quant_combine t_3 l pq st); [entailer! | auto | auto].
Qed.

Lemma proof_of_thm_apply_return_wit_1_2 : thm_apply_return_wit_1_2.
Proof.
  pre_process.
  Exists (thm_subst' t_2 l) (SRBool 1).
  unfold store_solve_res, restypeID.
  unfold thm_subst_allres_rel in H1.
  entailer!.
  + sep_apply (partial_quant_combine t_2 l pq st); [entailer! | auto | auto].
  + unfold thm_app_rel, thm_app in H7.
  rewrite H1 in H7.
  unfold term_alpha_eqn in H0.
  destruct term_alpha_eq eqn:Heq; [ | congruence].
  auto.
Qed.

Lemma store_sub_thm_res_zero: forall thm_pre t_2 l,
  store_sub_thm_res thm_pre 0 t_2 l |-- [| thm_subst_allres t_2 l = None |] && store_term thm_pre (thm_subst' t_2 l).
Proof.
  intros.
  unfold store_sub_thm_res.
  destruct thm_subst_allres eqn:Heq.
  + destruct p.
  sep_apply (store_null_right t (store_partial_quant thm_pre 0 p)
      ([|Some (p, t) = None|] && store_term thm_pre (thm_subst' t_2 l))
  ).
  entailer!.
  + entailer!.
Qed. 

Lemma proof_of_thm_apply_return_wit_1_3 : thm_apply_return_wit_1_3.
Proof.
  pre_process.
  Exists (thm_subst' t_2 l) (SRBool 0).
  subst.
  sep_apply store_sub_thm_res_zero.
  unfold store_solve_res, restypeID.
  entailer!.
  unfold thm_app_rel, thm_app in H4.
  rewrite H in H4.
  auto.
Qed.

Lemma proof_of_thm_apply_which_implies_wit_1 : thm_apply_which_implies_wit_1.
Proof. 
  pre_process.
  unfold store_solve_res.
  Exists 0 0.
  entailer!.
Qed.

Lemma proof_of_thm_apply_which_implies_wit_2 : thm_apply_which_implies_wit_2.
Proof.
  pre_process.
  unfold store_sub_thm_res.
  destruct (thm_subst_allres t l) eqn:Heq; [ | entailer!].
  destruct p.
  Exists p t0.
  entailer!.
Qed.

Lemma proof_of_thm_apply_which_implies_wit_3 : thm_apply_which_implies_wit_3.
Proof.
  pre_process.
  Exists 0; subst.
  entailer!.
Admitted. 

Lemma proof_of_thm_apply_which_implies_wit_4 : thm_apply_which_implies_wit_4.
Proof.
  pre_process.
  entailer!.
  unfold thm_app_rel, thm_app in H1.
  unfold thm_subst_allres_rel in H0.
  rewrite H0 in H1.
  unfold term_alpha_eqn in H.
  destruct term_alpha_eq; [ congruence | ].
  unfold get_list in *.
  auto.
Qed.

Lemma proof_of_check_list_gen_derive_low_level_spec_aux_by_low_level_spec : check_list_gen_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  pre_process.
  eapply safeExec_bind in H as (X' & ? & ?).
  Exists theo targ X'.
  entailer!.
  apply derivable1_wand_sepcon_adjoint.
  Intros t2 l2 r2; Exists t2 l2 r2.
  entailer!.
Qed.
