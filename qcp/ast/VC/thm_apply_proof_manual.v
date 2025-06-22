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
Import naive_C_Rules.
From SimpleC.EE Require Import ast_lib.
From SimpleC.EE Require Import malloc.
From SimpleC.EE Require Import sll_tmpl.
Local Open Scope sac.


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
    lia.
  - sep_apply store_term_fold_out.
    entailer!.
    entailer!.
    lia.
  - contradiction.
  - sep_apply store_term_fold_out.
    entailer!.
    entailer!.
    lia.
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
  destruct llctype.
  - unfold ctID in H; lia.
  - unfold ctID in H; lia.
  - unfold ctID in H; lia.
  - unfold ctID in H; lia.
  - unfold ctID in H; lia.
  - unfold ctID in H; lia.
  - unfold ctID in H; lia.
  - Exists t1' t2'.
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

Lemma proof_of_thm_apply_return_wit_1_1 : thm_apply_return_wit_1_1.
Proof.
  pre_process.
  Exists retval_3.
  unfold thm_subst_allres_rel in H2.
  unfold store_sub_thm_res.
  rewrite H2.
  entailer!.    
  unfold thm_app.
  rewrite H2.
  rewrite H0 in H1; unfold term_alpha_eqn in H1.
  destruct (term_alpha_eq st g) eqn:Heq; [ congruence | ].
  unfold store_solve_res.
  Exists retval_2.
  unfold restypeID.
  entailer!.
Qed.

Lemma proof_of_thm_apply_return_wit_1_2 : thm_apply_return_wit_1_2.
Proof.
  pre_process.
  Exists retval_3.
  unfold thm_subst_allres_rel in H1.
  unfold store_sub_thm_res; rewrite H1.
  unfold thm_app; rewrite H1.
  unfold term_alpha_eqn in H0.
  destruct (term_alpha_eq st g) eqn:Heq; [ | congruence ].
  unfold store_solve_res, restypeID.
  entailer!.
Qed.

Lemma proof_of_thm_apply_return_wit_1_3 : thm_apply_return_wit_1_3.
Proof.
  pre_process.
  Exists retval_2.
  rewrite H.
  unfold store_sub_thm_res.
  unfold thm_app.
  destruct (thm_subst_allres t l).
  + destruct p.
    unfold store_term at 1.
    destruct t0; unfold NULL.
    - entailer!; Intros y; congruence.
    - entailer!; Intros y; congruence.
    - entailer!; Intros y z; congruence.
    - entailer!; Intros y z; congruence.
  + unfold store_solve_res.
    entailer!.
Qed. 

Lemma proof_of_thm_apply_which_implies_wit_1 : thm_apply_which_implies_wit_1.
Proof.
  pre_process.
  unfold store_solve_res, restypeID.
  Exists 0 0.
  entailer!.
Qed.

Lemma proof_of_thm_apply_which_implies_wit_2 : thm_apply_which_implies_wit_2.
Proof.
  pre_process.
  unfold store_sub_thm_res, thm_subst_allres_rel.
  destruct (thm_subst_allres t l).
  + destruct p.
    Exists p t0.
    entailer!.
  + entailer!.
Qed.  

Lemma proof_of_thm_apply_which_implies_wit_3 : thm_apply_which_implies_wit_3.
Proof.
  pre_process.
  Exists 0; rewrite H.
  entailer!.
Admitted.
