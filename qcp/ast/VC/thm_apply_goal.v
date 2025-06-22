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

(*----- Function sub_thm -----*)

Definition sub_thm_safety_wit_1 := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) ,
  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sub_thm_safety_wit_2 := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) ,
  [| (thm_pre <> 0) |] 
  &&  [| (l = (cons (vs) (l0))) |] 
  &&  [| (lis_pre <> 0) |]
  &&  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition sub_thm_safety_wit_3 := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) ,
  [| ((termtypeID (t)) <> 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (l = (cons (vs) (l0))) |] 
  &&  [| (lis_pre <> 0) |]
  &&  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sub_thm_return_wit_1 := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) ,
  [| (lis_pre = 0) |]
  &&  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
|--
  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre thm_pre t l )
.

Definition sub_thm_return_wit_2 := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (sz: Z) (sy: Z) (z: Z) (y: Z) (sv: (@list Z)) (st: term) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval_2: Z) (retval: Z) ,
  [| (retval_2 = z) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (lis_cur <> 0) |] 
  &&  [| (t = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (vs = (VarSub (sv) (st))) |] 
  &&  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (l = (cons (vs) (l0))) |] 
  &&  [| (lis_pre <> 0) |]
  &&  (sll_var_sub_list lis_next l0 )
  **  (store_sub_thm_res retval_2 retval (term_subst_t (st) (sv) (qterm)) l0 )
  **  (store_term sz st )
  **  (store_string sy sv )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> retval_2)
  **  (store_string y qvar )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
|--
  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
.

Definition sub_thm_return_wit_3 := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) ,
  [| ((termtypeID (t)) <> 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (l = (cons (vs) (l0))) |] 
  &&  [| (lis_pre <> 0) |]
  &&  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre 0 t l )
.

Definition sub_thm_partial_solve_wit_1_pure := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) ,
  [| (lis_pre <> 0) |]
  &&  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
|--
  [| (lis_pre <> 0) |]
.

Definition sub_thm_partial_solve_wit_1_aux := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) ,
  [| (lis_pre <> 0) |]
  &&  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
|--
  [| (lis_pre <> 0) |] 
  &&  [| (lis_pre <> 0) |]
  &&  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
.

Definition sub_thm_partial_solve_wit_1 := sub_thm_partial_solve_wit_1_pure -> sub_thm_partial_solve_wit_1_aux.

Definition sub_thm_partial_solve_wit_2_pure := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) ,
  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (l = (cons (vs) (l0))) |] 
  &&  [| (lis_pre <> 0) |]
  &&  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |]
.

Definition sub_thm_partial_solve_wit_2_aux := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) ,
  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (l = (cons (vs) (l0))) |] 
  &&  [| (lis_pre <> 0) |]
  &&  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (l = (cons (vs) (l0))) |] 
  &&  [| (lis_pre <> 0) |]
  &&  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm_pre t )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
.

Definition sub_thm_partial_solve_wit_2 := sub_thm_partial_solve_wit_2_pure -> sub_thm_partial_solve_wit_2_aux.

Definition sub_thm_partial_solve_wit_3_pure := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (sz: Z) (sy: Z) (z: Z) (y: Z) (sv: (@list Z)) (st: term) (qt: quant_type) (qvar: (@list Z)) (qterm: term) ,
  [| (thm_pre <> 0) |] 
  &&  [| (lis_cur <> 0) |] 
  &&  [| (t = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (vs = (VarSub (sv) (st))) |] 
  &&  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (l = (cons (vs) (l0))) |] 
  &&  [| (lis_pre <> 0) |]
  &&  ((( &( "den" ) )) # Ptr  |-> sz)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  (store_string sy sv )
  **  (store_term sz st )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  [| (z <> 0) |] 
  &&  [| (sy <> 0) |] 
  &&  [| (sz <> 0) |]
.

Definition sub_thm_partial_solve_wit_3_aux := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (sz: Z) (sy: Z) (z: Z) (y: Z) (sv: (@list Z)) (st: term) (qt: quant_type) (qvar: (@list Z)) (qterm: term) ,
  [| (thm_pre <> 0) |] 
  &&  [| (lis_cur <> 0) |] 
  &&  [| (t = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (vs = (VarSub (sv) (st))) |] 
  &&  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (l = (cons (vs) (l0))) |] 
  &&  [| (lis_pre <> 0) |]
  &&  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  (store_string sy sv )
  **  (store_term sz st )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  [| (z <> 0) |] 
  &&  [| (sy <> 0) |] 
  &&  [| (sz <> 0) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (lis_cur <> 0) |] 
  &&  [| (t = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (vs = (VarSub (sv) (st))) |] 
  &&  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (l = (cons (vs) (l0))) |] 
  &&  [| (lis_pre <> 0) |]
  &&  (store_term z qterm )
  **  (store_string sy sv )
  **  (store_term sz st )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
.

Definition sub_thm_partial_solve_wit_3 := sub_thm_partial_solve_wit_3_pure -> sub_thm_partial_solve_wit_3_aux.

Definition sub_thm_partial_solve_wit_4 := 
forall (lis_pre: Z) (thm_pre: Z) (l: (@list var_sub)) (t: term) (lis_next: Z) (lis_cur: Z) (vs: var_sub) (l0: (@list var_sub)) (sz: Z) (sy: Z) (z: Z) (y: Z) (sv: (@list Z)) (st: term) (qt: quant_type) (qvar: (@list Z)) (qterm: term) (retval: Z) ,
  [| (retval = z) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (lis_cur <> 0) |] 
  &&  [| (t = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (vs = (VarSub (sv) (st))) |] 
  &&  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (l = (cons (vs) (l0))) |] 
  &&  [| (lis_pre <> 0) |]
  &&  (store_term retval (term_subst_t (st) (sv) (qterm)) )
  **  (store_term sz st )
  **  (store_string sy sv )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> retval)
  **  (store_string y qvar )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
|--
  [| (retval = z) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (lis_cur <> 0) |] 
  &&  [| (t = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (vs = (VarSub (sv) (st))) |] 
  &&  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm_pre <> 0) |] 
  &&  [| (l = (cons (vs) (l0))) |] 
  &&  [| (lis_pre <> 0) |]
  &&  (store_term retval (term_subst_t (st) (sv) (qterm)) )
  **  (sll_var_sub_list lis_next l0 )
  **  (store_term sz st )
  **  (store_string sy sv )
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm_pre)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> retval)
  **  (store_string y qvar )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  ((&((lis_pre)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
.

Definition sub_thm_which_implies_wit_1 := 
forall (l: (@list var_sub)) (t: term) (lis: Z) (thm: Z) ,
  [| (lis <> 0) |]
  &&  (store_term thm t )
  **  (sll_var_sub_list lis l )
|--
  EX (lis_next: Z)  (lis_cur: Z)  (vs: var_sub)  (l0: (@list var_sub)) ,
  [| (thm <> 0) |] 
  &&  [| (l = (cons (vs) (l0))) |]
  &&  ((&((thm)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm t )
  **  ((&((lis)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
  **  ((&((lis)  # "var_sub_list" ->ₛ "next")) # Ptr  |-> lis_next)
  **  (sll_var_sub_list lis_next l0 )
.

Definition sub_thm_which_implies_wit_2 := 
forall (t: term) (vs: var_sub) (thm: Z) (lis: Z) (lis_cur: Z) ,
  [| ((termtypeID (t)) = 3) |] 
  &&  [| (thm <> 0) |]
  &&  ((&((thm)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  (store_term' thm t )
  **  ((&((lis)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  (store_var_sub lis_cur vs )
|--
  EX (sz: Z)  (sy: Z)  (z: Z)  (y: Z)  (sv: (@list Z))  (st: term)  (qt: quant_type)  (qvar: (@list Z))  (qterm: term) ,
  [| (thm <> 0) |] 
  &&  [| (lis_cur <> 0) |] 
  &&  [| (t = (TermQuant (qt) (qvar) (qterm))) |] 
  &&  [| (vs = (VarSub (sv) (st))) |]
  &&  ((&((lis)  # "var_sub_list" ->ₛ "cur")) # Ptr  |-> lis_cur)
  **  ((&((thm)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (t)))
  **  ((&((thm)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "type")) # Int  |-> (qtID (qt)))
  **  ((&((thm)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "var")) # Ptr  |-> y)
  **  ((&((thm)  # "term" ->ₛ "content" .ₛ "Quant" .ₛ "body")) # Ptr  |-> z)
  **  (store_string y qvar )
  **  (store_term z qterm )
  **  ((&((lis_cur)  # "var_sub" ->ₛ "var")) # Ptr  |-> sy)
  **  ((&((lis_cur)  # "var_sub" ->ₛ "sub_term")) # Ptr  |-> sz)
  **  (store_string sy sv )
  **  (store_term sz st )
.

(*----- Function separate_imply -----*)

Definition separate_imply_safety_wit_1 := 
forall (t_pre: Z) (trm: term) ,
  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition separate_imply_safety_wit_2 := 
forall (t_pre: Z) (trm: term) ,
  [| ((termtypeID (trm)) <> 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition separate_imply_safety_wit_3 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) ,
  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v_2 lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition separate_imply_safety_wit_4 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) ,
  [| ((termtypeID (lt)) <> 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v_2 lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition separate_imply_safety_wit_5 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) ,
  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v_4 ll )
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition separate_imply_safety_wit_6 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) ,
  [| ((termtypeID (ll)) <> 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v_4 ll )
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition separate_imply_safety_wit_7 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (llctype: const_type) (llcctnt: Z) ,
  [| (ll = (TermConst (llctype) (llcctnt))) |] 
  &&  [| ((termtypeID (ll)) = 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (7 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 7) |]
.

Definition separate_imply_safety_wit_8 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (llctype: const_type) (llcctnt: Z) ,
  [| ((ctID (llctype)) <> 7) |] 
  &&  [| (ll = (TermConst (llctype) (llcctnt))) |] 
  &&  [| ((termtypeID (ll)) = 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition separate_imply_return_wit_1 := 
forall (t_pre: Z) (trm: term) ,
  [| ((termtypeID (trm)) <> 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
|--
  (store_imply_res 0 (sep_impl (trm)) )
  **  (store_term t_pre trm )
.

Definition separate_imply_return_wit_2 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) ,
  [| ((termtypeID (lt)) <> 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v_2 lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res 0 (sep_impl (trm)) )
  **  (store_term t_pre trm )
.

Definition separate_imply_return_wit_3 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) ,
  [| ((termtypeID (ll)) <> 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v_4 ll )
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res 0 (sep_impl (trm)) )
  **  (store_term t_pre trm )
.

Definition separate_imply_return_wit_4 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (llctype: const_type) (llcctnt: Z) ,
  [| ((ctID (llctype)) <> 7) |] 
  &&  [| (ll = (TermConst (llctype) (llcctnt))) |] 
  &&  [| ((termtypeID (ll)) = 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res 0 (sep_impl (trm)) )
  **  (store_term t_pre trm )
.

Definition separate_imply_return_wit_5 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (llctype: const_type) (llcctnt: Z) (t1': Z) (t2': Z) (retval: Z) ,
  [| ((ctID (llctype)) = 7) |] 
  &&  [| (ll = (TermConst (llctype) (llcctnt))) |] 
  &&  [| ((termtypeID (ll)) = 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  (store_term v_3 lr )
  **  (store_term v rt )
  **  (store_ImplyProp retval t1' t2' lr rt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  (store_imply_res retval (sep_impl (trm)) )
  **  (store_term t_pre trm )
.

Definition separate_imply_partial_solve_wit_1 := 
forall (t_pre: Z) (trm: term) ,
  (store_term t_pre trm )
|--
  (store_term t_pre trm )
.

Definition separate_imply_partial_solve_wit_2_pure := 
forall (t_pre: Z) (trm: term) ,
  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
|--
  [| (t_pre <> 0) |] 
  &&  [| ((termtypeID (trm)) = 2) |]
.

Definition separate_imply_partial_solve_wit_2_aux := 
forall (t_pre: Z) (trm: term) ,
  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t_pre trm )
|--
  [| (t_pre <> 0) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  (store_term' t_pre trm )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
.

Definition separate_imply_partial_solve_wit_2 := separate_imply_partial_solve_wit_2_pure -> separate_imply_partial_solve_wit_2_aux.

Definition separate_imply_partial_solve_wit_3 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) ,
  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term v_2 lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term v_2 lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
.

Definition separate_imply_partial_solve_wit_4_pure := 
forall (t_pre: Z) (trm: term) (v_2: Z) (v: Z) (lt: term) (rt: term) ,
  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_2)
  **  (store_term v_2 rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (v <> 0) |] 
  &&  [| ((termtypeID (lt)) = 2) |]
.

Definition separate_imply_partial_solve_wit_4_aux := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) ,
  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v_2 lt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (v_2 <> 0) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term' v_2 lt )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
.

Definition separate_imply_partial_solve_wit_4 := separate_imply_partial_solve_wit_4_pure -> separate_imply_partial_solve_wit_4_aux.

Definition separate_imply_partial_solve_wit_5 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) ,
  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  (store_term v_4 ll )
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  (store_term v_4 ll )
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
.

Definition separate_imply_partial_solve_wit_6_pure := 
forall (t_pre: Z) (trm: term) (v_2: Z) (v_3: Z) (lt: term) (rt: term) (v_4: Z) (v: Z) (ll: term) (lr: term) ,
  [| ((termtypeID (ll)) = 1) |] 
  &&  [| (v <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_3 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_3)
  **  ((&((v_3)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v ll )
  **  ((&((v_3)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_4)
  **  (store_term v_4 lr )
  **  ((&((v_3)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_2)
  **  (store_term v_2 rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (v <> 0) |] 
  &&  [| ((termtypeID (ll)) = 1) |]
.

Definition separate_imply_partial_solve_wit_6_aux := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) ,
  [| ((termtypeID (ll)) = 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v_4 ll )
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| (v_4 <> 0) |] 
  &&  [| ((termtypeID (ll)) = 1) |] 
  &&  [| ((termtypeID (ll)) = 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  (store_term' v_4 ll )
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
.

Definition separate_imply_partial_solve_wit_6 := separate_imply_partial_solve_wit_6_pure -> separate_imply_partial_solve_wit_6_aux.

Definition separate_imply_partial_solve_wit_7 := 
forall (t_pre: Z) (trm: term) (v: Z) (v_2: Z) (lt: term) (rt: term) (v_3: Z) (v_4: Z) (ll: term) (lr: term) (llctype: const_type) (llcctnt: Z) ,
  [| ((ctID (llctype)) = 7) |] 
  &&  [| (ll = (TermConst (llctype) (llcctnt))) |] 
  &&  [| ((termtypeID (ll)) = 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  (store_term v_3 lr )
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
|--
  [| ((ctID (llctype)) = 7) |] 
  &&  [| (ll = (TermConst (llctype) (llcctnt))) |] 
  &&  [| ((termtypeID (ll)) = 1) |] 
  &&  [| (v_4 <> 0) |] 
  &&  [| (lt = (TermApply (ll) (lr))) |] 
  &&  [| ((termtypeID (lt)) = 2) |] 
  &&  [| (v_2 <> 0) |] 
  &&  [| (trm = (TermApply (lt) (rt))) |] 
  &&  [| ((termtypeID (trm)) = 2) |] 
  &&  [| (t_pre <> 0) |]
  &&  (store_term v_3 lr )
  **  (store_term v rt )
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_4)
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_4)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
  **  ((&((v_4)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v_3)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  ((&((t_pre)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  ((&((t_pre)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
.

Definition separate_imply_which_implies_wit_1 := 
forall (trm: term) (t: Z) ,
  (store_term t trm )
|--
  [| (t <> 0) |]
  &&  ((&((t)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (trm)))
  **  (store_term' t trm )
.

Definition separate_imply_which_implies_wit_2 := 
forall (trm: term) (t: Z) ,
  [| (t <> 0) |] 
  &&  [| ((termtypeID (trm)) = 2) |]
  &&  (store_term' t trm )
|--
  EX (v: Z)  (v_2: Z)  (lt: term)  (rt: term) ,
  [| (trm = (TermApply (lt) (rt))) |]
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term v_2 lt )
  **  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v rt )
.

Definition separate_imply_which_implies_wit_3 := 
forall (lt: term) (t: Z) (v: Z) ,
  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  (store_term v lt )
|--
  [| (v <> 0) |]
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (lt)))
  **  (store_term' v lt )
.

Definition separate_imply_which_implies_wit_4 := 
forall (lt: term) (t: Z) (v_3: Z) ,
  [| (v_3 <> 0) |] 
  &&  [| ((termtypeID (lt)) = 2) |]
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_3)
  **  (store_term' v_3 lt )
|--
  EX (v: Z)  (v_2: Z)  (ll: term)  (lr: term) ,
  [| (lt = (TermApply (ll) (lr))) |]
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_3)
  **  ((&((v_3)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term v_2 ll )
  **  ((&((v_3)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right")) # Ptr  |-> v)
  **  (store_term v lr )
.

Definition separate_imply_which_implies_wit_5 := 
forall (ll: term) (t: Z) (v: Z) (v_2: Z) ,
  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term v_2 ll )
|--
  [| (v_2 <> 0) |]
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "type")) # Int  |-> (termtypeID (ll)))
  **  (store_term' v_2 ll )
.

Definition separate_imply_which_implies_wit_6 := 
forall (ll: term) (t: Z) (v: Z) (v_2: Z) ,
  [| (v_2 <> 0) |] 
  &&  [| ((termtypeID (ll)) = 1) |]
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  (store_term' v_2 ll )
|--
  EX (llctype: const_type)  (llcctnt: Z) ,
  [| (ll = (TermConst (llctype) (llcctnt))) |]
  &&  ((&((t)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v)
  **  ((&((v)  # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "type")) # Int  |-> (ctID (llctype)))
  **  ((&((v_2)  # "term" ->ₛ "content" .ₛ "Const" .ₛ "content")) # Int  |-> llcctnt)
.

(*----- Function thm_apply -----*)

Definition thm_apply_safety_wit_1 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) ,
  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term goal_pre g )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition thm_apply_safety_wit_2 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) ,
  [| (retval = 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term goal_pre g )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition thm_apply_safety_wit_3 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) ,
  [| (retval = 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 0)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term goal_pre g )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition thm_apply_safety_wit_4 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval_2: Z) (retval_3: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (term_alpha_eqn (st) (g))) |] 
  &&  [| (thm_subst_allres_rel t l pq st ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_3 <> 0) |]
  &&  (store_term retval_2 st )
  **  (store_term goal_pre g )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval_2)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_partial_quant thm_pre retval_2 pq )
  **  ((( &( "res" ) )) # Ptr  |-> retval_3)
  **  ((&((retval_3)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_3)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition thm_apply_safety_wit_5 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval_2: Z) (retval_3: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = (term_alpha_eqn (st) (g))) |] 
  &&  [| (thm_subst_allres_rel t l pq st ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_3 <> 0) |]
  &&  (store_term retval_2 st )
  **  (store_term goal_pre g )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval_2)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_partial_quant thm_pre retval_2 pq )
  **  ((( &( "res" ) )) # Ptr  |-> retval_3)
  **  ((&((retval_3)  # "solve_res" ->ₛ "type")) # Int  |-> 0)
  **  ((&((retval_3)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition thm_apply_safety_wit_6 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval_2: Z) (retval_3: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (st) (g))) |] 
  &&  [| (thm_subst_allres_rel t l pq st ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_3 <> 0) |]
  &&  (store_term retval_2 st )
  **  (store_term goal_pre g )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval_2)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_partial_quant thm_pre retval_2 pq )
  **  ((( &( "res" ) )) # Ptr  |-> retval_3)
  **  ((&((retval_3)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_3)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition thm_apply_return_wit_1_1 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval_3: Z) (retval: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_4: Z) (v_2: Z) (retval_2: Z) ,
  [| (v_2 = 0) |] 
  &&  [| (retval_4 = 0) |] 
  &&  [| (retval_4 = (term_alpha_eqn (st) (g))) |] 
  &&  [| (thm_subst_allres_rel t l pq st ) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval <> 0) |]
  &&  (store_term retval_3 st )
  **  (store_term goal_pre g )
  **  (sll_term_list retval_2 (gen_pre (st) (g)) )
  **  ((&((retval)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> retval_2)
  **  (store_partial_quant thm_pre retval_3 pq )
  **  ((&((retval)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
|--
  EX (ti: Z) ,
  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
  **  (store_solve_res retval (thm_app (t) (l) (g)) )
  **  (store_sub_thm_res thm_pre ti t l )
.

Definition thm_apply_return_wit_1_2 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval_3: Z) (retval: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 = (term_alpha_eqn (st) (g))) |] 
  &&  [| (thm_subst_allres_rel t l pq st ) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval <> 0) |]
  &&  (store_term retval_3 st )
  **  (store_term goal_pre g )
  **  (store_partial_quant thm_pre retval_3 pq )
  **  ((&((retval)  # "solve_res" ->ₛ "type")) # Int  |-> 0)
  **  ((&((retval)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
|--
  EX (ti: Z) ,
  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
  **  (store_solve_res retval (thm_app (t) (l) (g)) )
  **  (store_sub_thm_res thm_pre ti t l )
.

Definition thm_apply_return_wit_1_3 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval_2: Z) (retval: Z) (v: Z) (res_type: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval <> 0) |]
  &&  ((&((retval)  # "solve_res" ->ₛ "type")) # Int  |-> 0)
  **  ((&((retval)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> 0)
  **  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval_2 t l )
  **  (store_term goal_pre g )
|--
  EX (ti: Z) ,
  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
  **  (store_solve_res retval (thm_app (t) (l) (g)) )
  **  (store_sub_thm_res thm_pre ti t l )
.

Definition thm_apply_partial_solve_wit_1 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) ,
  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
|--
  (store_term thm_pre t )
  **  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
.

Definition thm_apply_partial_solve_wit_2 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) ,
  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
  **  (store_term goal_pre g )
|--
  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
  **  (store_term goal_pre g )
.

Definition thm_apply_partial_solve_wit_3 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |]
  &&  (store_solve_res retval_2 (SRBool (0)) )
  **  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
  **  (store_term goal_pre g )
|--
  [| (retval_2 <> 0) |]
  &&  (store_solve_res retval_2 (SRBool (0)) )
  **  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
  **  (store_term goal_pre g )
.

Definition thm_apply_partial_solve_wit_4_pure := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) ,
  [| (retval <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  ((( &( "res" ) )) # Ptr  |-> retval_2)
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval)
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_term goal_pre g )
|--
  [| (retval <> 0) |]
.

Definition thm_apply_partial_solve_wit_4_aux := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) ,
  [| (retval <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_sub_thm_res thm_pre retval t l )
  **  (store_term goal_pre g )
|--
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (store_sub_thm_res thm_pre retval t l )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
.

Definition thm_apply_partial_solve_wit_4 := thm_apply_partial_solve_wit_4_pure -> thm_apply_partial_solve_wit_4_aux.

Definition thm_apply_partial_solve_wit_5 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) ,
  [| (thm_subst_allres_rel t l pq st ) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (store_partial_quant thm_pre retval pq )
  **  (store_term retval st )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  (store_term goal_pre g )
|--
  [| (thm_subst_allres_rel t l pq st ) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (store_term retval st )
  **  (store_term goal_pre g )
  **  (store_partial_quant thm_pre retval pq )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
.

Definition thm_apply_partial_solve_wit_6_pure := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval_2: Z) (retval_3: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = (term_alpha_eqn (st) (g))) |] 
  &&  [| (thm_subst_allres_rel t l pq st ) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_3 <> 0) |]
  &&  (store_term retval_2 st )
  **  (store_term goal_pre g )
  **  ((( &( "thm_ins" ) )) # Ptr  |-> retval_2)
  **  ((( &( "thm" ) )) # Ptr  |-> thm_pre)
  **  (store_partial_quant thm_pre retval_2 pq )
  **  ((( &( "res" ) )) # Ptr  |-> retval_3)
  **  ((&((retval_3)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  ((&((retval_3)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
  **  ((( &( "goal" ) )) # Ptr  |-> goal_pre)
  **  ((( &( "lis" ) )) # Ptr  |-> lis_pre)
|--
  [| (v = 0) |]
.

Definition thm_apply_partial_solve_wit_6_aux := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_3: Z) ,
  [| (retval_3 = 0) |] 
  &&  [| (retval_3 = (term_alpha_eqn (st) (g))) |] 
  &&  [| (thm_subst_allres_rel t l pq st ) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (store_term retval st )
  **  (store_term goal_pre g )
  **  (store_partial_quant thm_pre retval pq )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (sll_var_sub_list lis_pre l )
|--
  [| (v = 0) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_3 = (term_alpha_eqn (st) (g))) |] 
  &&  [| (thm_subst_allres_rel t l pq st ) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
  **  (store_term retval st )
  **  (store_term goal_pre g )
  **  (store_partial_quant thm_pre retval pq )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
.

Definition thm_apply_partial_solve_wit_6 := thm_apply_partial_solve_wit_6_pure -> thm_apply_partial_solve_wit_6_aux.

Definition thm_apply_partial_solve_wit_7 := 
forall (goal_pre: Z) (lis_pre: Z) (thm_pre: Z) (g: term) (l: (@list var_sub)) (t: term) (retval: Z) (retval_2: Z) (v: Z) (res_type: Z) (pq: partial_quant) (st: term) (retval_3: Z) (v_2: Z) ,
  [| (v_2 = 0) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_3 = (term_alpha_eqn (st) (g))) |] 
  &&  [| (thm_subst_allres_rel t l pq st ) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> v_2)
  **  (store_term retval st )
  **  (store_term goal_pre g )
  **  (store_partial_quant thm_pre retval pq )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
|--
  [| (v_2 = 0) |] 
  &&  [| (retval_3 = 0) |] 
  &&  [| (retval_3 = (term_alpha_eqn (st) (g))) |] 
  &&  [| (thm_subst_allres_rel t l pq st ) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (res_type = 0) |] 
  &&  [| (v = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (store_term retval st )
  **  (store_term goal_pre g )
  **  ((&((retval_2)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> v_2)
  **  (store_partial_quant thm_pre retval pq )
  **  ((&((retval_2)  # "solve_res" ->ₛ "type")) # Int  |-> 1)
  **  (sll_var_sub_list lis_pre l )
.

Definition thm_apply_which_implies_wit_1 := 
forall (res: Z) ,
  (store_solve_res res (SRBool (0)) )
|--
  EX (v: Z)  (res_type: Z) ,
  [| (res_type = 0) |] 
  &&  [| (v = 0) |]
  &&  ((&((res)  # "solve_res" ->ₛ "type")) # Int  |-> res_type)
  **  ((&((res)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v)
.

Definition thm_apply_which_implies_wit_2 := 
forall (l: (@list var_sub)) (t: term) (thm_ins: Z) (thm: Z) ,
  [| (thm_ins <> 0) |]
  &&  (store_sub_thm_res thm thm_ins t l )
|--
  EX (pq: partial_quant)  (st: term) ,
  [| (thm_subst_allres_rel t l pq st ) |]
  &&  (store_partial_quant thm thm_ins pq )
  **  (store_term thm_ins st )
.

Definition thm_apply_which_implies_wit_3 := 
forall (res: Z) (v_2: Z) ,
  [| (v_2 = 0) |]
  &&  ((&((res)  # "solve_res" ->ₛ "d" .ₛ "ans")) # Int  |-> v_2)
|--
  EX (v: Z) ,
  [| (v = 0) |]
  &&  ((&((res)  # "solve_res" ->ₛ "d" .ₛ "list")) # Ptr  |-> v)
.

Module Type VC_Correct.

Axiom proof_of_sub_thm_safety_wit_1 : sub_thm_safety_wit_1.
Axiom proof_of_sub_thm_safety_wit_2 : sub_thm_safety_wit_2.
Axiom proof_of_sub_thm_safety_wit_3 : sub_thm_safety_wit_3.
Axiom proof_of_sub_thm_return_wit_1 : sub_thm_return_wit_1.
Axiom proof_of_sub_thm_return_wit_2 : sub_thm_return_wit_2.
Axiom proof_of_sub_thm_return_wit_3 : sub_thm_return_wit_3.
Axiom proof_of_sub_thm_partial_solve_wit_1_pure : sub_thm_partial_solve_wit_1_pure.
Axiom proof_of_sub_thm_partial_solve_wit_1 : sub_thm_partial_solve_wit_1.
Axiom proof_of_sub_thm_partial_solve_wit_2_pure : sub_thm_partial_solve_wit_2_pure.
Axiom proof_of_sub_thm_partial_solve_wit_2 : sub_thm_partial_solve_wit_2.
Axiom proof_of_sub_thm_partial_solve_wit_3_pure : sub_thm_partial_solve_wit_3_pure.
Axiom proof_of_sub_thm_partial_solve_wit_3 : sub_thm_partial_solve_wit_3.
Axiom proof_of_sub_thm_partial_solve_wit_4 : sub_thm_partial_solve_wit_4.
Axiom proof_of_sub_thm_which_implies_wit_1 : sub_thm_which_implies_wit_1.
Axiom proof_of_sub_thm_which_implies_wit_2 : sub_thm_which_implies_wit_2.
Axiom proof_of_separate_imply_safety_wit_1 : separate_imply_safety_wit_1.
Axiom proof_of_separate_imply_safety_wit_2 : separate_imply_safety_wit_2.
Axiom proof_of_separate_imply_safety_wit_3 : separate_imply_safety_wit_3.
Axiom proof_of_separate_imply_safety_wit_4 : separate_imply_safety_wit_4.
Axiom proof_of_separate_imply_safety_wit_5 : separate_imply_safety_wit_5.
Axiom proof_of_separate_imply_safety_wit_6 : separate_imply_safety_wit_6.
Axiom proof_of_separate_imply_safety_wit_7 : separate_imply_safety_wit_7.
Axiom proof_of_separate_imply_safety_wit_8 : separate_imply_safety_wit_8.
Axiom proof_of_separate_imply_return_wit_1 : separate_imply_return_wit_1.
Axiom proof_of_separate_imply_return_wit_2 : separate_imply_return_wit_2.
Axiom proof_of_separate_imply_return_wit_3 : separate_imply_return_wit_3.
Axiom proof_of_separate_imply_return_wit_4 : separate_imply_return_wit_4.
Axiom proof_of_separate_imply_return_wit_5 : separate_imply_return_wit_5.
Axiom proof_of_separate_imply_partial_solve_wit_1 : separate_imply_partial_solve_wit_1.
Axiom proof_of_separate_imply_partial_solve_wit_2_pure : separate_imply_partial_solve_wit_2_pure.
Axiom proof_of_separate_imply_partial_solve_wit_2 : separate_imply_partial_solve_wit_2.
Axiom proof_of_separate_imply_partial_solve_wit_3 : separate_imply_partial_solve_wit_3.
Axiom proof_of_separate_imply_partial_solve_wit_4_pure : separate_imply_partial_solve_wit_4_pure.
Axiom proof_of_separate_imply_partial_solve_wit_4 : separate_imply_partial_solve_wit_4.
Axiom proof_of_separate_imply_partial_solve_wit_5 : separate_imply_partial_solve_wit_5.
Axiom proof_of_separate_imply_partial_solve_wit_6_pure : separate_imply_partial_solve_wit_6_pure.
Axiom proof_of_separate_imply_partial_solve_wit_6 : separate_imply_partial_solve_wit_6.
Axiom proof_of_separate_imply_partial_solve_wit_7 : separate_imply_partial_solve_wit_7.
Axiom proof_of_separate_imply_which_implies_wit_1 : separate_imply_which_implies_wit_1.
Axiom proof_of_separate_imply_which_implies_wit_2 : separate_imply_which_implies_wit_2.
Axiom proof_of_separate_imply_which_implies_wit_3 : separate_imply_which_implies_wit_3.
Axiom proof_of_separate_imply_which_implies_wit_4 : separate_imply_which_implies_wit_4.
Axiom proof_of_separate_imply_which_implies_wit_5 : separate_imply_which_implies_wit_5.
Axiom proof_of_separate_imply_which_implies_wit_6 : separate_imply_which_implies_wit_6.
Axiom proof_of_thm_apply_safety_wit_1 : thm_apply_safety_wit_1.
Axiom proof_of_thm_apply_safety_wit_2 : thm_apply_safety_wit_2.
Axiom proof_of_thm_apply_safety_wit_3 : thm_apply_safety_wit_3.
Axiom proof_of_thm_apply_safety_wit_4 : thm_apply_safety_wit_4.
Axiom proof_of_thm_apply_safety_wit_5 : thm_apply_safety_wit_5.
Axiom proof_of_thm_apply_safety_wit_6 : thm_apply_safety_wit_6.
Axiom proof_of_thm_apply_return_wit_1_1 : thm_apply_return_wit_1_1.
Axiom proof_of_thm_apply_return_wit_1_2 : thm_apply_return_wit_1_2.
Axiom proof_of_thm_apply_return_wit_1_3 : thm_apply_return_wit_1_3.
Axiom proof_of_thm_apply_partial_solve_wit_1 : thm_apply_partial_solve_wit_1.
Axiom proof_of_thm_apply_partial_solve_wit_2 : thm_apply_partial_solve_wit_2.
Axiom proof_of_thm_apply_partial_solve_wit_3 : thm_apply_partial_solve_wit_3.
Axiom proof_of_thm_apply_partial_solve_wit_4_pure : thm_apply_partial_solve_wit_4_pure.
Axiom proof_of_thm_apply_partial_solve_wit_4 : thm_apply_partial_solve_wit_4.
Axiom proof_of_thm_apply_partial_solve_wit_5 : thm_apply_partial_solve_wit_5.
Axiom proof_of_thm_apply_partial_solve_wit_6_pure : thm_apply_partial_solve_wit_6_pure.
Axiom proof_of_thm_apply_partial_solve_wit_6 : thm_apply_partial_solve_wit_6.
Axiom proof_of_thm_apply_partial_solve_wit_7 : thm_apply_partial_solve_wit_7.
Axiom proof_of_thm_apply_which_implies_wit_1 : thm_apply_which_implies_wit_1.
Axiom proof_of_thm_apply_which_implies_wit_2 : thm_apply_which_implies_wit_2.
Axiom proof_of_thm_apply_which_implies_wit_3 : thm_apply_which_implies_wit_3.

End VC_Correct.
