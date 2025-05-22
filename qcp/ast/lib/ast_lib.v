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
Local Open Scope string.
From SimpleC.EE Require Import sll_tmpl.

Import naive_C_Rules.
Local Open Scope sac.

Definition var_name : Type := list Z.


(* all about ast basic structure *)
Module ast_def.

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

End ast_def.

Import ast_def.

Definition termtypeID (t: term) : Z :=
  match t with
    | TermVar _ => 0%Z
    | TermConst _ _ => 1%Z
    | TermApply _ _ => 2%Z
    | TermQuant _ _ _ => 3%Z
  end.

(* Definition zlength {A: Type} (l: list A) : Z :=
  Z.of_nat (List.length l). *)

Fixpoint all_zero_list_nat (n: nat) : list Z :=
  match n with
    | O => nil
    | S n0 => 0 :: (all_zero_list_nat n0)
  end.

Definition all_zero_list (n: Z): list Z :=
  all_zero_list_nat (Z.to_nat n).

Definition store_string (x: addr) (str: var_name): Assertion :=
  EX n: Z,
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
                                  &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var") # Ptr |-> y **
                                  &(x # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body") # Ptr |-> z **
                                  store_string y qvar ** store_term z body
  end.

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

Module ast_var_sub.

Inductive var_sub : Type :=
  | VarSub (name: var_name) (t: term): var_sub.

Definition var_sub_list : Type := list var_sub.

End ast_var_sub.

Import ast_var_sub.

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

Module ast_solve_res.

Inductive res_type : Type :=
  | BoolRes: res_type
  | TermList: res_type.

Inductive solve_res : Type :=
  | SRBool (ans: Z): solve_res
  | SRTList (l: term_list): solve_res.

End ast_solve_res.

Import ast_solve_res.

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

(* all about ImplyProp *)

Module ast_imply_prop.

Inductive ImplyProp : Type :=
  | ImplP (assum: term) (concl: term): ImplyProp.

Definition store_ImplyProp (x: addr) (p: ImplyProp): Assertion :=
  match p with
    | ImplP assum concl => [| x <> NULL |] &&
                           EX y z: addr,
                            &(x # "ImplyProp" ->ₛ "assum") # Ptr |-> y **
                            &(x # "ImplyProp" ->ₛ "concl") # Ptr |-> z **
                            store_term y assum ** store_term z concl
  end.

End ast_imply_prop.

Import ast_imply_prop.
