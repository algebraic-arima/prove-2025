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

Fixpoint term_not_contain_var (t : term) (var : var_name) : Prop :=
  match t with
    | TermVar v => list_Z_eqb v var = false
    | TermConst ctype content => True
    | TermApply lt rt => term_not_contain_var lt var /\ term_not_contain_var rt var
    | TermQuant qtype qvar body => list_Z_eqb var qvar = false /\ term_not_contain_var body var
end.

Fixpoint free_vars (t: term) : list var_name :=
  match t with
  | TermVar v => [v]
  | TermConst _ _ => []
  | TermApply f x => free_vars f ++ free_vars x
  | TermQuant _ qvar body =>
      List.filter (fun v => negb (list_Z_eqb v qvar)) (free_vars body)
  end.

Fixpoint term_size (t: term) : Z :=
  match t with
  | TermVar _ => 1
  | TermConst _ _ => 1
  | TermApply f x => 1 + term_size f + term_size x
  | TermQuant _ _ body => 1 + term_size body
  end.

Lemma term_size_p: forall t,
  term_size t > 0.
Proof.
  unfold term_size.
  induction t; try lia.
Qed.

Lemma term_subst_v_non_increase: forall old new t,
  term_size (term_subst_v old new t) = term_size t.
Proof.
  unfold term_subst_v.
  induction t.
  + destruct (list_Z_eqb var new) eqn:Heq; [ | reflexivity].
    unfold term_size; reflexivity.
  + reflexivity.
  + fold term_subst_v in *.
    unfold term_size; fold term_size; lia.
  + fold term_subst_v in *.
    destruct (list_Z_eqb qvar new) eqn:Heq; [reflexivity | ].
    unfold term_size; fold term_size; lia.
Qed.

Program Fixpoint term_alpha_eq (t1 t2: term) 
  {measure (Z.to_nat (term_size t1) + Z.to_nat (term_size t2))} : Prop :=
  match t1, t2 with
  | TermVar v1, TermVar v2 => v1 = v2
  | TermConst ctype1 content1, TermConst ctype2 content2 =>
      ctID ctype1 = ctID ctype2 /\
      (ctID ctype1 <> 0 \/ content1 = content2)
  | TermApply lt1 rt1, TermApply lt2 rt2 =>
      term_alpha_eq lt1 lt2 /\ term_alpha_eq rt1 rt2
  | TermQuant qtype1 qvar1 body1, TermQuant qtype2 qvar2 body2 =>
      qtID qtype1 = qtID qtype2 /\
      qtID qtype1 = qtID qtype2 /\
      exists fresh, 
        term_not_contain_var t1 fresh /\
        term_not_contain_var t2 fresh /\
        term_alpha_eq 
          (term_subst_v qvar1 fresh body1) 
          (term_subst_v qvar2 fresh body2)
  | _, _ => False
  end.
  
Next Obligation.
  unfold term_size; fold term_size.
  pose proof term_size_p lt1.
  pose proof term_size_p lt2.
  pose proof term_size_p rt1.
  pose proof term_size_p rt2.
  rewrite !Z2Nat.inj_add; try lia.
Qed.

Definition term_eqn (t1 t2: term): Prop :=
  term_alpha_eq t1 t2.

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


Lemma list_Z_eqb_refl : forall (l : list Z),
  list_Z_eqb l l = true.
Proof.
  intros.
  apply list_Z_eqb_eq.
  reflexivity.
Qed.

Lemma list_Z_eqb_symm : forall (l1 l2 : list Z),
  list_Z_eqb l1 l2 = true ->
  list_Z_eqb l2 l1 = true.
Proof.
  intros.
  apply list_Z_eqb_eq.
  pose proof list_Z_eqb_eq l1 l2.
  destruct H0 as [H0 _].
  pose proof H0 H.
  auto.
Qed.

Lemma list_Z_eqb_trans : forall (l1 l2 l3 : list Z),
  list_Z_eqb l1 l2 = true ->
  list_Z_eqb l2 l3 = true ->
  list_Z_eqb l1 l3 = true.
Proof.
  intros.
  apply list_Z_eqb_eq.
  pose proof list_Z_eqb_eq l1 l2.
  pose proof list_Z_eqb_eq l2 l3.
  destruct H1 as [H1 _]; destruct H2 as [H2 _].
  pose proof H1 H; pose proof H2 H0.
  rewrite H3, H4.
  reflexivity.
Qed.

Lemma term_eqb_symm : forall (t1 t2 : term),
  term_eqb t1 t2 = true ->
  term_eqb t2 t1 = true.
Proof.
  induction t1.
  + destruct t2; try discriminate.
    unfold term_eqb in *.
    apply list_Z_eqb_symm; auto.
  + destruct t2; try discriminate.
    intros.
    unfold term_eqb in *.
    rewrite andb_true_iff, orb_true_iff in *.
    rewrite Z.eqb_eq in *.
    destruct H as [Ha Hb].
    split; [auto | ].
    rewrite <- Ha.
    destruct Hb.
    - left; auto.
    - right; rewrite Z.eqb_eq in *; auto.  
  + destruct t2; try discriminate.
    unfold term_eqb in *.
    fold term_eqb in *.
    intros; rewrite andb_true_iff in *; destruct H as [Ha Hb].
    pose proof IHt1_1 t2_1 Ha.
    pose proof IHt1_2 t2_2 Hb.
    auto.
  + destruct t2; try discriminate.
    unfold term_eqb in *.
    fold term_eqb in *.
    intros; rewrite andb_true_iff in *; destruct H as [Ha Hb].
    rewrite Z.eqb_eq in *.
    split; [auto | ].
Admitted.

Lemma term_subst_v_same_name : forall (den src : var_name) (t : term),
  list_Z_eqb den src = true ->
  term_eqb (term_subst_v den src t) t = true.
Proof.
  intros d s t.
  revert d s.
  induction t.
  + intros.
    unfold term_subst_v.
    destruct (list_Z_eqb var s) eqn:Heq.
    - pose proof list_Z_eqb_symm var s Heq.
      pose proof list_Z_eqb_trans d s var H H0.
      exact H1.
    - apply list_Z_eqb_refl.
  + intros.
    unfold term_subst_v.
    unfold term_eqb.
    rewrite andb_true_iff, orb_true_iff in *.
    split.
    - rewrite Z.eqb_eq.
      reflexivity.
    - rewrite Z.eqb_eq.
      right; reflexivity.
  + intros.
    unfold term_subst_v.
    fold term_subst_v.
    unfold term_eqb.
    fold term_eqb.
    rewrite andb_true_iff.
    split; [ apply (IHt1 d s H) |  apply (IHt2 d s H)].
  + intros.
    unfold term_subst_v.
    fold term_subst_v.
    destruct (list_Z_eqb qvar s) eqn:Heq.
    - unfold term_eqb.
      fold term_eqb.
      rewrite andb_true_iff; split.
      * rewrite Z.eqb_eq; reflexivity.
      * pose proof IHt d s H.
        pose proof list_Z_eqb_eq d s.
        pose proof list_Z_eqb_eq qvar s.
        destruct H1 as [H1 _].
        destruct H2 as [H2 _].
        pose proof H1 H; pose proof H2 Heq.
        rewrite H4.
        rewrite H3 in H0.

Admitted. 
