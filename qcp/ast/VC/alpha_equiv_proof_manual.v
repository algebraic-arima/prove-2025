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
Require Import alpha_equiv_goal.
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

Lemma proof_of_alpha_equiv_entail_wit_1_1 : alpha_equiv_entail_wit_1_1.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_entail_wit_1_2 : alpha_equiv_entail_wit_1_2.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_return_wit_1_1 : alpha_equiv_return_wit_1_1.
Proof. 
    pre_process.
    unfold list_Z_cmp in H0.
    destruct (list_Z_eqb str1 str2) eqn:Heq; [ contradiction | ].
    unfold store_term, term_alpha_eqn, prop_to_z.
    rewrite H3, H4.
    Exists y z.
    entailer!.
    destruct (term_alpha_eq_dec (TermVar str1) (TermVar str2)) as [Halpha | Hnotalpha].
    + inversion Halpha.
      pose proof list_Z_eq2eqb str1 str2 H13.
      congruence.
    + reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_1_2 : alpha_equiv_return_wit_1_2.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_return_wit_2 : alpha_equiv_return_wit_2.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_return_wit_3_1 : alpha_equiv_return_wit_3_1.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_return_wit_3_2 : alpha_equiv_return_wit_3_2.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_return_wit_4 : alpha_equiv_return_wit_4.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_return_wit_5_1 : alpha_equiv_return_wit_5_1.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_return_wit_5_2 : alpha_equiv_return_wit_5_2.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_return_wit_5_3 : alpha_equiv_return_wit_5_3.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_return_wit_6 : alpha_equiv_return_wit_6.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_return_wit_7 : alpha_equiv_return_wit_7.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_return_wit_8_1 : alpha_equiv_return_wit_8_1.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_return_wit_8_2 : alpha_equiv_return_wit_8_2.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_return_wit_9 : alpha_equiv_return_wit_9.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_partial_solve_wit_15_pure : alpha_equiv_partial_solve_wit_15_pure.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_partial_solve_wit_17_pure : alpha_equiv_partial_solve_wit_17_pure.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_partial_solve_wit_21_pure : alpha_equiv_partial_solve_wit_21_pure.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_which_implies_wit_1 : alpha_equiv_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_which_implies_wit_2 : alpha_equiv_which_implies_wit_2.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_which_implies_wit_3 : alpha_equiv_which_implies_wit_3.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_which_implies_wit_4 : alpha_equiv_which_implies_wit_4.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_which_implies_wit_5 : alpha_equiv_which_implies_wit_5.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_which_implies_wit_6 : alpha_equiv_which_implies_wit_6.
Proof. Admitted. 

Lemma proof_of_alpha_equiv_which_implies_wit_7 : alpha_equiv_which_implies_wit_7.
Proof. Admitted. 

