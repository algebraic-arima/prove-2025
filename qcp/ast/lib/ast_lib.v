Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Require Import Coq.Program.Wf.
Local Open Scope string.
From SimpleC.EE Require Import sll_tmpl.
From SimpleC.EE Require Import malloc.

Import naive_C_Rules.
Local Open Scope sac.

Definition var_name : Type := list Z.

(* all about ast basic structure *)

Inductive const_type : Type :=
  | CNum: const_type
  | CAdd: const_type
  | CMul: const_type
  | CEq: const_type
  | CLe: const_type
  | CAnd: const_type
  | COr: const_type
  | CImpl: const_type.

Inductive quant_type : Type :=
  | QForall: quant_type
  | QExists: quant_type.

Inductive term_type : Type :=
  | TVar: term_type
  | TConst: term_type
  | TApply: term_type
  | TQuant: term_type.
  
Definition ctID (t: const_type) :=
  match t with
    | CNum => 0%Z
    | CAdd => 1%Z
    | CMul => 2%Z
    | CEq => 3%Z
    | CLe => 4%Z
    | CAnd => 5%Z
    | COr => 6%Z
    | CImpl => 7%Z
  end.
  
Definition qtID (t: quant_type) :=
  match t with
    | QForall => 0%Z
    | QExists => 1%Z
  end.

Definition ttID (t: term_type) :=
  match t with
    | TVar => 0%Z
    | TConst => 1%Z
    | TApply => 2%Z
    | TQuant => 3%Z
  end.

Inductive term : Type :=
  | TermVar (var: var_name): term
  | TermConst (ctype: const_type) (content: Z): term
  | TermApply (lt: term) (rt: term): term
  | TermQuant (qtype: quant_type) (qvar: var_name) (body: term): term.

Definition term_list : Type := list term.

Definition termtypeID (t: term) : Z :=
  match t with
    | TermVar _ => 0%Z
    | TermConst _ _ => 1%Z
    | TermApply _ _ => 2%Z
    | TermQuant _ _ _ => 3%Z
  end.

(* Definition zlength {A: Type} (l: list A) : Z :=
  Z.of_nat (List.length l). *)

Definition store_string (x: addr) (str: var_name): Assertion :=
  EX n: Z,
  [| x <> NULL |] &&
  [| n >= 0 |] &&
  store_char_array x (Zlength (str ++ (all_zero_list n))) (str ++ (all_zero_list n)).

Fixpoint store_term (x: addr) (t: term): Assertion :=
  [| x <> NULL |] && &(x # "term" ->ₛ "type") # Int |-> termtypeID t **
  match t with
    | TermVar var => EX y: addr,
                    &(x # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> y **
                    store_string y var
    | TermConst ctype content => &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID ctype **
                                &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> content
    | TermApply lt rt => EX y z: addr,
                        &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y **
                        &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z **
                        store_term y lt ** store_term z rt
    | TermQuant qtype qvar body => EX y z: addr,
                                  &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qtype **
                                  &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y **
                                  &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z **
                                  store_string y qvar ** store_term z body
  end.

Definition store_term' (x: addr) (t: term): Assertion :=
  match t with
    | TermVar var => EX y: addr,
                      &(x # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> y **
                      store_string y var
    | TermConst ctype content => &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID ctype **
                                 &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> content
    | TermApply lt rt => EX y z: addr,
                          &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y **
                          &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z **
                          store_term y lt ** store_term z rt
    | TermQuant qtype qvar body => EX y z: addr,
                                    &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qtype **
                                    &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y **
                                    &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z **
                                    store_string y qvar ** store_term z body
  end.

Lemma store_term_unfold: forall x t,
  store_term x t |--
  [| x <> NULL |] &&
  &(x # "term" ->ₛ "type") # Int |-> termtypeID t **
  store_term' x t.
Proof.
  intros.
  unfold store_term, store_term'.
  destruct t; fold store_term; entailer!.
Qed.

Lemma store_term_fold: forall x t,
  [| x <> NULL |] &&
  &(x # "term" ->ₛ "type") # Int |-> termtypeID t **
  store_term' x t |--
  store_term x t.
Proof.
  intros.
  unfold store_term, store_term'.
  destruct t; fold store_term; entailer!.
Qed.

Lemma store_term'_Var: forall x t,
  termtypeID t = 0%Z ->
  x <> NULL ->
  store_term' x t |--
  EX var, [| t = TermVar var |] && [| x <> NULL |] &&
  EX y: addr,
    &(x # "term" ->ₛ "content" .ₛ "Var") # Ptr |-> y **
    store_string y var.
Proof.
  intros.
  unfold store_term'.
  induction t; try discriminate.
  Intros y.
  Exists var y.
  entailer!.
Qed.

Lemma store_term'_Const: forall x t,
  termtypeID t = 1%Z ->
  x <> NULL ->
  store_term' x t |--
  EX ctype content, [| t = TermConst ctype content |] && [| x <> NULL |] &&
  &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID ctype **
  &(x # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> content.
Proof.
  intros.
  unfold store_term'.
  induction t; try discriminate.
  Intros.
  Exists ctype content.
  entailer!.
Qed.

Lemma store_term'_Apply: forall x t,
  termtypeID t = 2%Z ->
  x <> NULL ->
  store_term' x t |--
  EX lt rt, [| t = TermApply lt rt |] && [| x <> NULL |] &&
  EX y z: addr,
    &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y **
    &(x # "term" ->ₛ "content" .ₛ "Apply" .ₛ  "right") # Ptr |-> z **
    store_term y lt ** store_term z rt.
Proof.
  intros.
  unfold store_term'.
  induction t; try discriminate.
  Intros y z.
  Exists t1 t2 y z.
  entailer!.
Qed.

Lemma store_term'_Quant: forall x t,
  termtypeID t = 3%Z ->
  x <> NULL ->
  store_term' x t |--
  EX qtype qvar body, [| t = TermQuant qtype qvar body |] && [| x <> NULL |] &&
  EX y z: addr,
    &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type") # Int |-> qtID qtype **
    &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y **
    &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z **
    store_string y qvar ** store_term z body.
Proof.
  intros.
  unfold store_term'.
  induction t; try discriminate.
  Intros y z.
  Exists qtype qvar t y z.
  entailer!.
Qed.

Definition store_term_cell (x: addr) (t: term): Assertion :=
  [| x <> NULL |] &&
  EX y: addr,
    &(x # "term_list" ->ₛ "element") # Ptr |-> y **
    store_term y t.

Definition sll_term_list (x: addr) (l: term_list): Assertion :=
  sll store_term_cell "term_list" "next" x l.

Definition sllseg_term_list (x: addr) (y: addr) (l: term_list): Assertion :=
  sllseg store_term_cell "term_list" "next" x y l.

Definition sllbseg_term_list (x: addr) (y: addr) (l: term_list): Assertion :=
  sllbseg store_term_cell "term_list" "next" x y l.
    

(* all about ast var_sub *)

Inductive var_sub : Type :=
  | VarSub (name: var_name) (t: term): var_sub.

Definition var_sub_list : Type := list var_sub.


(* Definition var_sub_list : Type := list var_sub. *)
(* v is stored on addr x *)
Definition store_var_sub (x: addr) (v: var_sub): Assertion :=
  match v with
    | VarSub name term => [| x <> NULL |] &&
                          EX y z: addr,
                           &(x # "var_sub" ->ₛ "var") # Ptr |-> y **
                           &(x # "var_sub" ->ₛ "sub_term") # Ptr |-> z **
                           store_string y name ** store_term z term
  end.

(* the linked list node stores the var_sub type addr *)
Definition store_var_sub_cell (x: addr) (v: var_sub): Assertion :=
  [| x <> NULL |] &&
  EX y: addr, 
    &(x # "var_sub_list" ->ₛ "cur") # Ptr |-> y **
    store_var_sub y v.

Definition sll_var_sub_list (x: addr) (l: var_sub_list): Assertion :=
  sll store_var_sub_cell "var_sub_list" "next" x l.

Definition sllseg_var_sub_list (x: addr) (y: addr) (l: var_sub_list): Assertion :=
  sllseg store_var_sub_cell "var_sub_list" "next" x y l.

Definition sllbseg_var_sub_list (x: addr) (y: addr) (l: var_sub_list): Assertion :=
  sllbseg store_var_sub_cell "var_sub_list" "next" x y l.


(* all about ast solve result *)

Inductive res_type : Type :=
  | BoolRes: res_type
  | TermList: res_type.

Inductive solve_res : Type :=
  | SRBool (ans: Z): solve_res
  | SRTList (l: term_list): solve_res.


Definition restypeID (sr : solve_res) : Z :=
  match sr with
    | SRBool _ => 0%Z
    | SRTList _ => 1%Z
  end.

Definition store_solve_res (x: addr) (sr: solve_res): Assertion :=
  [| x <> NULL |] && &(x # "solve_res" ->ₛ "type") # Int |-> restypeID sr **
  match sr with
    | SRBool ans => &(x # "solve_res" ->ₛ "content" .ₛ "Bool") # Int |-> ans
    | SRTList l => EX y: addr,
                   &(x # "solve_res" ->ₛ "content" .ₛ "TermList") # Ptr |-> y **
                   sll_term_list y l
  end.

Definition store_solve_res' (x: addr) (sr: solve_res): Assertion :=
  match sr with
    | SRBool ans => [| x <> NULL |] && &(x # "solve_res" ->ₛ "content" .ₛ "Bool") # Int |-> ans
    | SRTList l => [| x <> NULL |] && EX y: addr,
                   &(x # "solve_res" ->ₛ "content" .ₛ "TermList") # Ptr |-> y **
                   sll_term_list y l
  end.

Lemma store_solve_res_unfold: forall x sr,
  store_solve_res x sr |--
  &(x # "solve_res" ->ₛ "type") # Int |-> restypeID sr **
  store_solve_res' x sr.
Proof.
  intros.
  unfold store_solve_res, store_solve_res'.
  destruct sr; fold store_solve_res; entailer!.
Qed.

Lemma store_solve_res_fold: forall x sr,
  &(x # "solve_res" ->ₛ "type") # Int |-> restypeID sr **
  store_solve_res' x sr |--
  store_solve_res x sr.
Proof.
  intros.
  unfold store_solve_res, store_solve_res'.
  destruct sr; fold store_solve_res; entailer!.
Qed.

Lemma store_solve_res'_Bool: forall x sr,
  restypeID sr = 0%Z ->
  store_solve_res' x sr |--
  EX ans, [| sr = SRBool ans |] && [| x <> NULL |] &&
  &(x # "solve_res" ->ₛ "content" .ₛ "Bool") # Int |-> ans.
Proof.
  intros.
  unfold store_solve_res'.
  induction sr; try discriminate.
  Intros.
  Exists ans.
  entailer!.
Qed.

Lemma store_solve_res'_List: forall x sr,
  restypeID sr = 1%Z ->
  store_solve_res' x sr |--
  EX l, [| sr = SRTList l |] && [| x <> NULL |] &&
  EX y: addr,
    &(x # "solve_res" ->ₛ "content" .ₛ "TermList") # Ptr |-> y **
    sll_term_list y l.
Proof.
  intros.
  unfold store_solve_res'.
  induction sr; try discriminate.
  Intros y.
  Exists l y.
  entailer!.
Qed.

(* all about ImplyProp *)

Inductive ImplyProp : Type :=
  | ImplP (assum: term) (concl: term): ImplyProp.

Definition store_ImplyProp (x y z: addr) (assum concl: term): Assertion :=
  [| x <> NULL |] &&
  &(x # "ImplyProp" ->ₛ "assum") # Ptr |-> y **
  &(x # "ImplyProp" ->ₛ "concl") # Ptr |-> z **
  store_term y assum ** store_term z concl.


Fixpoint list_Z_eqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: t1, x2 :: t2 => Z.eqb x1 x2 && list_Z_eqb t1 t2
  | _, _ => false
  end.

Definition list_Z_cmp (l1 l2 : list Z) : Z :=
  if list_Z_eqb l1 l2 then 0 else 1.

Fixpoint term_subst_v (den src: var_name) (t: term): term :=
  match t with
    | TermVar v => if list_Z_eqb v src then TermVar den else TermVar v
    | TermConst ctype content => TermConst ctype content
    | TermApply lt rt => TermApply (term_subst_v den src lt) (term_subst_v den src rt)
    | TermQuant qtype qvar body =>
      if list_Z_eqb qvar src then
        TermQuant qtype qvar body
      else
        TermQuant qtype qvar (term_subst_v den src body)
  end.

Fixpoint term_subst_t (den: term) (src: var_name) (t: term): term :=
  match t with
    | TermVar v => if list_Z_eqb v src then den else TermVar v
    | TermConst ctype content => TermConst ctype content
    | TermApply lt rt => TermApply (term_subst_t den src lt) (term_subst_t den src rt)
    | TermQuant qtype qvar body =>
      if list_Z_eqb qvar src then
        TermQuant qtype qvar body
      else
        TermQuant qtype qvar (term_subst_t den src body)
  end.

Lemma list_Z_eqb_eq : forall l1 l2 : list Z,
  list_Z_eqb l1 l2 = true <-> l1 = l2.
Proof. 
  induction l1.
  + intros.
    destruct l2; [ split; try reflexivity | split; try discriminate ].
  + intros.
    destruct l2; [ split; try discriminate | split ].
    - unfold list_Z_eqb.
      fold list_Z_eqb.
      rewrite andb_true_iff.
      intros.
      destruct H as [Ha Hl].
      rewrite Z.eqb_eq in Ha.
      pose proof IHl1 l2.
      destruct H.
      pose proof H Hl.
      rewrite Ha, H1.
      reflexivity.
    - intros.
      injection H.
      intros.
      unfold list_Z_eqb.
      fold list_Z_eqb.
      rewrite andb_true_iff.
      pose proof IHl1 l2.
      destruct H2.
      pose proof H3 H0.
      split; [ | auto].
      rewrite Z.eqb_eq.
      auto.
Qed.

Lemma list_Z_eqb2eq : forall l1 l2 : list Z,
  list_Z_eqb l1 l2 = true -> l1 = l2.
Proof.
  apply list_Z_eqb_eq.
Qed. 

Lemma list_Z_eq2eqb : forall l1 l2 : list Z,
  l1 = l2 -> list_Z_eqb l1 l2 = true.
Proof.
  apply list_Z_eqb_eq.
Qed. 

Lemma list_Z_neqb_neq : forall l1 l2 : list Z,
  list_Z_eqb l1 l2 = false <-> l1 <> l2.
Proof.
  intros l1 l2. split.
  + intros H Hcontra.
    pose proof list_Z_eq2eqb l1 l2 Hcontra; congruence.
  + intros H.
    destruct (list_Z_eqb l1 l2) eqn:E.
    - pose proof list_Z_eqb2eq l1 l2 E; congruence.
    - reflexivity.  
Qed.

Lemma list_Z_neqb2neq : forall l1 l2 : list Z,
  list_Z_eqb l1 l2 = false -> l1 <> l2.
Proof.
  apply list_Z_neqb_neq.
Qed. 

Lemma list_Z_neq2neqb : forall l1 l2 : list Z,
  l1 <> l2 -> list_Z_eqb l1 l2 = false.
Proof.
  apply list_Z_neqb_neq.
Qed. 

Lemma list_Z_eqb_refl : forall (l : list Z),
  list_Z_eqb l l = true.
Proof.
  intros.
  apply list_Z_eqb_eq.
  reflexivity.
Qed.

Lemma list_Z_eqb_symm : forall (l1 l2 : list Z),
  list_Z_eqb l1 l2 = list_Z_eqb l2 l1.
Proof.
  intros.
  destruct (list_Z_eqb l1 l2) eqn:E.
  + pose proof list_Z_eqb2eq l1 l2 E.
    rewrite H; pose proof list_Z_eqb_refl l2; rewrite H0; auto.
  + pose proof list_Z_neqb2neq l1 l2 E.
    destruct (list_Z_eqb l2 l1) eqn:Heq.
    - pose proof list_Z_eqb2eq l2 l1 Heq; congruence.
    - auto.
Qed.

Lemma list_Z_eqb_trans : forall (l1 l2 l3 : list Z),
  list_Z_eqb l1 l2 = true ->
  list_Z_eqb l2 l3 = true ->
  list_Z_eqb l1 l3 = true.
Proof.
  intros.
  apply list_Z_eqb_eq.
  pose proof list_Z_eqb2eq l1 l2 H.
  pose proof list_Z_eqb2eq l2 l3 H0.
  rewrite H1, H2.
  reflexivity.
Qed.

(* alpha_equiv begin *)

Fixpoint term_not_contain_var (t : term) (var : var_name) : Prop :=
  match t with
  | TermVar v => v <> var
  | TermConst _ _ => True
  | TermApply lt rt => term_not_contain_var lt var /\ term_not_contain_var rt var
  | TermQuant _ qvar body => qvar <> var /\ term_not_contain_var body var
  end.

Fixpoint sub_thm (thm: term) (l: var_sub_list): term :=
  match l with 
    | nil => thm
    | (VarSub v t) :: l0 => 
      match thm with
        | TermQuant qtype qvar body =>
            sub_thm (term_subst_t t v body) l0
        | _ => thm
      end
  end.

(* Inductive term_alpha_eq : term -> term -> Prop :=
  | AlphaVar : forall v1 v2,
      v1 = v2 ->
      term_alpha_eq (TermVar v1) (TermVar v2)
  | AlphaConst : forall ctype1 content1 ctype2 content2,
      ctID ctype1 = ctID ctype2 ->
      (ctID ctype1 <> 0 \/ content1 = content2) ->
      term_alpha_eq (TermConst ctype1 content1) (TermConst ctype2 content2)
  | AlphaApply : forall lt1 rt1 lt2 rt2,
      term_alpha_eq lt1 lt2 -> term_alpha_eq rt1 rt2 ->
      term_alpha_eq (TermApply lt1 rt1) (TermApply lt2 rt2)
  | AlphaQuant : forall qtype1 qvar1 body1 qtype2 qvar2 body2,
      qtID qtype1 = qtID qtype2 ->
      (list_Z_eqb qvar1 qvar2 = true) /\ (term_alpha_eq body1 body2) \/
      (term_alpha_eq body1 (term_subst_v qvar1 qvar2 body2)) /\
      (term_alpha_eq (term_subst_v qvar2 qvar1 body1) body2) ->
      term_alpha_eq (TermQuant qtype1 qvar1 body1) (TermQuant qtype2 qvar2 body2). *)

Inductive term_alpha_eq : term -> term -> Prop :=
  | AlphaVar : forall v1 v2,
      v1 = v2 ->
      term_alpha_eq (TermVar v1) (TermVar v2)
  | AlphaConst : forall ctype1 content1 ctype2 content2,
      ctID ctype1 = ctID ctype2 ->
      (ctID ctype1 <> 0 \/ content1 = content2) ->
      term_alpha_eq (TermConst ctype1 content1) (TermConst ctype2 content2)
  | AlphaApply : forall lt1 rt1 lt2 rt2,
      term_alpha_eq lt1 lt2 -> term_alpha_eq rt1 rt2 ->
      term_alpha_eq (TermApply lt1 rt1) (TermApply lt2 rt2)
  | AlphaQuant : forall qtype1 qvar1 body1 qtype2 qvar2 body2,
      qtID qtype1 = qtID qtype2 ->
      (list_Z_eqb qvar1 qvar2 = true) /\ (term_alpha_eq body1 body2) \/
      (list_Z_eqb qvar1 qvar2 = false) /\ 
      (exists fresh,
        term_not_contain_var (TermQuant qtype1 qvar1 body1) fresh /\
        term_not_contain_var (TermQuant qtype2 qvar2 body2) fresh /\
        term_alpha_eq 
          (term_subst_v fresh qvar1 body1) 
          (term_subst_v fresh qvar2 body2)) ->
      term_alpha_eq (TermQuant qtype1 qvar1 body1) (TermQuant qtype2 qvar2 body2).

(* Lemma term_alpha_eq_var_eq : forall (v1 v2 : var_name),
  term_alpha_eq (TermVar v1) (TermVar v2) <-> (TermVar v1) = (TermVar v2).
Proof. *)

Lemma term_alpha_eq_refl : forall (t : term),
  term_alpha_eq t t.
Proof.
  induction t.
  + apply AlphaVar; reflexivity.
  + apply AlphaConst; [reflexivity | ].
    right; reflexivity.
  + apply AlphaApply; try auto.
  + apply AlphaQuant; [reflexivity | ].
    left; split; [ | apply IHt].
    apply list_Z_eq2eqb; reflexivity.
Qed.

Lemma term_alpha_eq_symm : forall (t1 t2 : term),
  term_alpha_eq t1 t2 ->
  term_alpha_eq t2 t1.
Proof.
  intros.
  revert t2 H; induction t1; simpl; intros.
  + destruct t2; try inversion H; try subst.
    apply AlphaVar; auto.
  + destruct t2; try inversion H; try subst.
    apply AlphaConst; rewrite <- H3; [auto | ].
    destruct H5; [ left; auto | right; rewrite H0; reflexivity].
  + destruct t2; try inversion H; try subst.
    apply AlphaApply.  
    pose proof IHt1_1 t2_1 H3.
    pose proof IHt1_2 t2_2 H5.
    auto. auto.
  + destruct t2; try inversion H; try subst.
    apply AlphaQuant; [auto | ].
    destruct H7 as [[Haa Hab]|[Hba Hbb]].
    - left; split.
      rewrite <- Haa.
      apply list_Z_eqb_symm.
      apply (IHt1 t2 Hab).
    - right; split.
      rewrite <- Hba.
      apply list_Z_eqb_symm.
      destruct Hbb as [x Hx]; exists x.
      destruct Hx as [Hxa [Hxb Hxc]].
      split; [auto | ].
      split; [auto | ].
Admitted.

Lemma term_alpha_eq_trans : forall (t1 t2 t3 : term),
  term_alpha_eq t1 t2 ->
  term_alpha_eq t2 t3 ->
  term_alpha_eq t1 t3.
Proof.
Admitted.

#[export] Instance term_alpha_eq_refl': Reflexive term_alpha_eq.
Proof. unfold Reflexive. apply term_alpha_eq_refl. Qed.

#[export] Instance term_alpha_eq_symm': Symmetric term_alpha_eq.
Proof. unfold Symmetric. apply term_alpha_eq_symm. Qed.

#[export] Instance term_alpha_eq_trans': Transitive term_alpha_eq.
Proof. unfold Transitive. apply term_alpha_eq_trans. Qed.

#[export] Instance term_alpha_eq_equiv: Equivalence term_alpha_eq.
Proof.
  split.
  + apply term_alpha_eq_refl'.
  + apply term_alpha_eq_symm'.
  + apply term_alpha_eq_trans'.
Qed.

Lemma term_subst_v_same_name : forall (den src : var_name) (t : term),
  list_Z_eqb den src = true ->
  term_alpha_eq (term_subst_v den src t) t.
Proof.
  induction t.
  + intros.
    unfold term_subst_v; fold term_subst_v.
    apply list_Z_eqb2eq in H.
    rewrite <- H.
    destruct list_Z_eqb eqn:Heq; [ | apply term_alpha_eq_refl].
    apply list_Z_eqb2eq in Heq.
    rewrite Heq.
    apply term_alpha_eq_refl.
  + intros.
    unfold term_subst_v; fold term_subst_v.
    apply term_alpha_eq_refl.
  + intros.
    unfold term_subst_v; fold term_subst_v.
    apply AlphaApply.
    auto. auto.
  + intros.
    unfold term_subst_v; fold term_subst_v.
    destruct (list_Z_eqb qvar src) eqn:Heq.
    - apply term_alpha_eq_refl.
    - apply AlphaQuant; [reflexivity | ].
      left. split.
      * apply list_Z_eq2eqb; reflexivity.
      * apply IHt, H.
Qed.

Lemma subst_not_contains: forall (t : term) (v1 v2 : var_name),
  term_not_contain_var t v2 ->
  term_alpha_eq t (term_subst_v v1 v2 t).
Proof.
  induction t; try intros; try unfold term_subst_v; try fold term_subst_v. 
  + unfold term_not_contain_var in H.
    destruct (list_Z_eqb var v2) eqn:Heq; try pose proof list_Z_eqb2eq var v2 Heq.
    - congruence.
    - apply AlphaVar; reflexivity.
  + unfold term_subst_v; apply AlphaConst; [auto | auto].
  + unfold term_not_contain_var in H; fold term_not_contain_var in H; destruct H.
    apply AlphaApply.
    apply (IHt1 v1 v2 H). apply (IHt2 v1 v2 H0).
  + destruct (list_Z_eqb qvar v2) eqn:Heqq.
    - apply term_alpha_eq_refl.
    - unfold term_not_contain_var in H; fold term_not_contain_var in H.
      apply AlphaQuant; [reflexivity | left; split; [apply list_Z_eqb_refl | ]].
      destruct H.
      apply (IHt v1 v2 H0).
Qed.

Lemma alpha_equiv_subst_rev: forall (t : term) (v1 v2 : var_name),
  term_not_contain_var t v1 ->
  term_not_contain_var t v2 ->
  term_alpha_eq t (term_subst_v v1 v2 (term_subst_v v2 v1 t)).
Proof.
  induction t; try intros.
  + unfold term_subst_v.
    destruct list_Z_eqb eqn:Heq.
    - pose proof list_Z_eqb2eq var v1 Heq.
      destruct (list_Z_eqb v2 v2) eqn:He; try apply AlphaVar.
      * auto.
      * pose proof list_Z_eqb_refl v2; congruence.
    - destruct (list_Z_eqb var v2) eqn:He; [ | apply AlphaVar; reflexivity].
      unfold term_not_contain_var in *.
      pose proof list_Z_eqb2eq var v2 He.
      destruct H; congruence.
  + unfold term_subst_v; apply AlphaConst; [auto | auto].
  + unfold term_not_contain_var in H, H0; fold term_not_contain_var in H, H0.
    destruct H as [Ha Hb].
    destruct H0 as [H0a H0b].
    unfold term_subst_v; fold term_subst_v; apply AlphaApply.
    apply (IHt1 v1 v2 Ha H0a). 
    apply (IHt2 v1 v2 Hb H0b).
  + unfold term_not_contain_var in H, H0; fold term_not_contain_var in H, H0.
    unfold term_subst_v; fold term_subst_v.
    destruct H as [Ha Hb].
    destruct H0 as [H0a H0b].
    destruct (list_Z_eqb qvar v1) eqn:Heq.
    - pose proof list_Z_eqb2eq qvar v1 Heq; congruence.
    - unfold term_subst_v; fold term_subst_v.
      destruct (list_Z_eqb qvar v2) eqn:Heqq.
      * pose proof list_Z_eqb2eq qvar v2 Heqq; congruence.
      * apply AlphaQuant; [reflexivity | left; split; [pose proof list_Z_eqb_refl qvar; auto | ]].
        apply (IHt v1 v2 Hb H0b).
Qed.

Lemma alpha_equiv_subst_trans: forall (t : term) (v1 v2 v3 : var_name),
  term_not_contain_var t v3 ->
  term_not_contain_var t v2 ->
  term_alpha_eq (term_subst_v v3 v1 t) (term_subst_v v3 v2 (term_subst_v v2 v1 t)).
Proof.
  induction t; try intros.
  + unfold term_subst_v.
    destruct list_Z_eqb eqn:Heq.
    - pose proof list_Z_eqb2eq var v1 Heq.
      destruct (list_Z_eqb v2 v2) eqn:He; try apply AlphaVar.
      * auto.
      * pose proof list_Z_eqb_refl v2; congruence.
    - destruct (list_Z_eqb var v2) eqn:He; [ | apply AlphaVar; reflexivity].
      unfold term_not_contain_var in *.
      pose proof list_Z_eqb2eq var v2 He.
      destruct H; congruence.
  + unfold term_subst_v; apply AlphaConst; [auto | auto].
  + unfold term_not_contain_var in H, H0; fold term_not_contain_var in H, H0.
    destruct H as [Ha Hb].
    destruct H0 as [H0a H0b].
    unfold term_subst_v; fold term_subst_v; apply AlphaApply.
    apply (IHt1 v1 v2 v3 Ha H0a). 
    apply (IHt2 v1 v2 v3 Hb H0b).
  + unfold term_not_contain_var in H, H0; fold term_not_contain_var in H, H0.
    unfold term_subst_v; fold term_subst_v.
    destruct H as [Ha Hb].
    destruct H0 as [H0a H0b].
    destruct (list_Z_eqb qvar v1) eqn:Heq.
    - unfold term_subst_v; fold term_subst_v.
      destruct (list_Z_eqb qvar v2) eqn:Heqq.
      * pose proof list_Z_eqb2eq qvar v2 Heqq; congruence.
      * apply AlphaQuant; [auto | left; split; [pose proof list_Z_eqb_refl qvar; auto | ]].
        apply (subst_not_contains t v3 v2 H0b).
    - unfold term_subst_v; fold term_subst_v.
      destruct (list_Z_eqb qvar v2) eqn:Heqq.
      * pose proof list_Z_eqb2eq qvar v2 Heqq; congruence.
      * apply AlphaQuant; [reflexivity | left; split; [pose proof list_Z_eqb_refl qvar; auto | ]].
        apply (IHt v1 v2 v3 Hb H0b).
Qed.

Lemma alpha_equiv_same_rename: forall (t1 t2 : term) (str1 str2 : list Z),
  (* term_not_contain_var t1 str1 /\
  term_not_contain_var t2 str1 /\ *)
  term_alpha_eq t1 t2 -> term_alpha_eq (term_subst_v str1 str2 t1) (term_subst_v str1 str2 t2).
Proof.
  intros.
  induction H; try unfold term_subst_v; try subst.
  + destruct list_Z_eqb; try apply AlphaVar; try reflexivity.
  + apply AlphaConst; [auto | auto].
  + fold term_subst_v; apply AlphaApply.
    auto. auto.
    (* unfold term_not_contain_var in Ha, Hb; fold term_not_contain_var in Ha, Hb.
    destruct Ha as [Haa Hab]; destruct Hb as [Hba Hbb].
    apply (IHterm_alpha_eq1 Haa Hba).
    destruct Ha as [Haa Hab]; destruct Hb as [Hba Hbb].
    apply (IHterm_alpha_eq2 Hab Hbb). *)
  + fold term_subst_v.
    destruct list_Z_eqb eqn:Heq; try destruct H0 as [Ha|Hb].
    - pose proof list_Z_eqb2eq qvar1 qvar2 Heq; subst.
      destruct (list_Z_eqb qvar2 str2) eqn:He.
      * apply AlphaQuant; [auto | left; split; destruct Ha as [Haa Hab]].
        { apply list_Z_eqb_refl. }
        { auto. }
        (* { destruct H0 as [[Eaa Eab]|[Eba Ebb]]; [auto | congruence]. } *)
      * apply AlphaQuant; [auto | left].
        split; [apply list_Z_eqb_refl | ].
        (* destruct H0 as [[Eaa Eab]|[Eba Ebb]]; [ | congruence]. *)
Admitted. 

Lemma alpha_equiv_quant: forall (t1 t2 : term) (qt1 qt2 : quant_type) (qv1 qv2 : var_name), 
  term_alpha_eq (TermQuant qt1 qv1 t1) (TermQuant qt2 qv2 t2) /\ list_Z_eqb qv1 qv2 = true -> 
  term_alpha_eq t1 t2.
Proof.
  intros t1 t2 qt1 qt2 qv1 qv2 [Halpha Heqv].
  pose proof (list_Z_eqb2eq qv1 qv2 Heqv) as Hqveq.
  inversion Halpha; subst.
  destruct H6 as [[? ?]|[? ?]].
  + destruct H; auto.
  + rewrite Heqv in H. congruence.
Qed.

Lemma alpha_equiv_quant_allvar: forall (t1 t2 : term) (qt1 qt2 : quant_type) (qv1 qv2 x : var_name), 
  term_alpha_eq (TermQuant qt1 qv1 t1) (TermQuant qt2 qv2 t2) /\ 
  term_not_contain_var (TermQuant qt1 qv1 t1) x /\
  term_not_contain_var (TermQuant qt2 qv2 t2) x /\
  list_Z_eqb qv1 qv2 = false -> 
  term_alpha_eq (term_subst_v x qv1 t1) (term_subst_v x qv2 t2).
Proof.
  intros.
  destruct H as [Ha [Hb Hc]].
  inversion Ha; subst.
  destruct H6 as [[Hla Hlb]|[Hra Hrb]].
  + destruct t1, t2; try inversion Hlb; destruct Hc as [Hd He]; try congruence.
  + destruct Hrb as [y [Hya [Hyb Hyc]]].
    destruct Hc as [Hca Hcb].
    unfold term_not_contain_var in Hb, Hca, Hya, Hyb; fold term_not_contain_var in Hb, Hca, Hya, Hyb.
    destruct Hb as [Hba Hbb]; destruct Hca as [Hcaa Hcab];
    destruct Hya as [Hyaa Hyab]; destruct Hyb as [Hyba Hybb].
    pose proof alpha_equiv_subst_trans t1 qv1 y x Hbb Hyab.
    pose proof alpha_equiv_subst_trans t2 qv2 y x Hcab Hybb.
    rewrite H.
    rewrite H0.
    apply (alpha_equiv_same_rename (term_subst_v y qv1 t1) (term_subst_v y qv2 t2) x y).
    exact Hyc.
Qed.