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

Lemma proof_of_sub_thm_return_wit_1 : sub_thm_return_wit_1.
Proof. Admitted. 

Lemma proof_of_sub_thm_return_wit_2 : sub_thm_return_wit_2.
Proof. Admitted. 

Lemma proof_of_sub_thm_return_wit_3 : sub_thm_return_wit_3.
Proof. Admitted. 

Lemma proof_of_sub_thm_partial_solve_wit_3_pure : sub_thm_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_sub_thm_which_implies_wit_1 : sub_thm_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_sub_thm_which_implies_wit_2 : sub_thm_which_implies_wit_2.
Proof. Admitted. 

Lemma proof_of_separate_imply_return_wit_1 : separate_imply_return_wit_1.
Proof. Admitted. 

Lemma proof_of_separate_imply_return_wit_2 : separate_imply_return_wit_2.
Proof. Admitted. 

Lemma proof_of_separate_imply_return_wit_3 : separate_imply_return_wit_3.
Proof. Admitted. 

Lemma proof_of_separate_imply_return_wit_4 : separate_imply_return_wit_4.
Proof. Admitted. 

Lemma proof_of_separate_imply_return_wit_5 : separate_imply_return_wit_5.
Proof. Admitted. 

Lemma proof_of_separate_imply_which_implies_wit_1 : separate_imply_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_separate_imply_which_implies_wit_2 : separate_imply_which_implies_wit_2.
Proof. Admitted. 

Lemma proof_of_separate_imply_which_implies_wit_3 : separate_imply_which_implies_wit_3.
Proof. Admitted. 

Lemma proof_of_separate_imply_which_implies_wit_4 : separate_imply_which_implies_wit_4.
Proof. Admitted. 

Lemma proof_of_separate_imply_which_implies_wit_5 : separate_imply_which_implies_wit_5.
Proof. Admitted. 

Lemma proof_of_separate_imply_which_implies_wit_6 : separate_imply_which_implies_wit_6.
Proof. Admitted. 

Lemma proof_of_check_list_gen_entail_wit_1 : check_list_gen_entail_wit_1.
Proof. Admitted. 


  Lemma store_term_cell_fold: forall x y t,
  x <> NULL ->
  &(x # "term_list" ->ₛ "element") # Ptr |-> y **
  store_term y t |--
  store_term_cell x t.
Proof.
  intros.
  unfold store_term_cell.
  Exists y.
  entailer!.
Qed.

Lemma sllbseg_one: forall a y retval,
  retval <> NULL ->
  y # Ptr |-> retval **
  store_term_cell retval a |--
  sllbseg_term_list y &(retval # "term_list" ->ₛ "next") (a::nil).
Proof.
  unfold sllbseg_term_list, sllbseg.
  intros.
  Exists retval.
  entailer!.
Qed.

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
Proof. Admitted. 

Lemma proof_of_check_list_gen_return_wit_2 : check_list_gen_return_wit_2.
Proof. Admitted. 

Lemma proof_of_check_list_gen_which_implies_wit_1 : check_list_gen_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_check_list_gen_which_implies_wit_2 : check_list_gen_which_implies_wit_2.
Proof. Admitted. 

Lemma proof_of_check_list_gen_which_implies_wit_3 : check_list_gen_which_implies_wit_3.
Proof. Admitted. 

Lemma proof_of_check_list_gen_which_implies_wit_4 : check_list_gen_which_implies_wit_4.
Proof. Admitted. 

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
  + unfold thm_app_rel, thm_app in H11.
    rewrite H5 in H11.
    rewrite H3 in H4.
    unfold term_alpha_eqn in H4.
    destruct term_alpha_eq eqn:Heq; [ congruence | ].
    prove_by_one_abs_step (t_2, l_2).
    unfold safeExec, safe in H, H0.
    unfold hs_eval.
    destruct H as [sa [Haa Hab]].
    destruct H0 as [sb [Hba Hbb]].
    intros.    
  Admitted. 

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
  Admitted. 

