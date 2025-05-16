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
Require Import sll_lib.
Require Import sll_merge_rel_lib.
Local Open Scope stmonad.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap relations.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import sll_strategy_goal.
From SimpleC.EE Require Import sll_strategy_proof.
From SimpleC.EE Require Import safeexec_strategy_goal.
From SimpleC.EE Require Import safeexec_strategy_proof.

(*----- Function split_while -----*)

Definition split_while_safety_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (X: (((@list Z) * (@list Z)) -> (unit -> Prop))) (p_pre_v: Z) (q_pre_v: Z) (q_v: Z) (p_v: Z) (x: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X ) |] 
  &&  [| (q_pre_v = 0) |] 
  &&  [| (p_pre_v = 0) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
  **  ((( &( "t" ) )) # Ptr  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition split_while_safety_wit_2 := 
forall (q_pre: Z) (p_pre: Z) (X: (((@list Z) * (@list Z)) -> (unit -> Prop))) (p_pre_v: Z) (q_pre_v: Z) (q_v: Z) (x: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) ,
  [| (safeExec ATrue (bind ((split_rec_rel (l1_new) (l2) ((cons (x_data) (l1))))) (reversepair)) X ) |] 
  &&  [| (l = (cons (x_data) (l1_new))) |] 
  &&  [| (x <> 0) |] 
  &&  [| (q_pre_v = 0) |] 
  &&  [| (p_pre_v = 0) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> x)
  **  (sll x (cons (x_data) (l1)) )
  **  ((( &( "x" ) )) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
  **  ((( &( "t" ) )) # Ptr  |-> x_next)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition split_while_entail_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (X: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_2: (@list Z)) (p_pre_v: Z) (q_pre_v: Z) ,
  [| (safeExec ATrue (split_rec_rel (l_2) (nil) (nil)) X ) |]
  &&  (sll x_pre l_2 )
  **  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v nil )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v nil )
|--
  EX (q_v: Z)  (p_v: Z)  (l: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  [| (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X ) |] 
  &&  [| (q_pre_v = 0) |] 
  &&  [| (p_pre_v = 0) |]
  &&  (sll x_pre l )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
.

Definition split_while_entail_wit_2 := 
forall (q_pre: Z) (p_pre: Z) (X: (((@list Z) * (@list Z)) -> (unit -> Prop))) (p_pre_v: Z) (q_pre_v: Z) (x: Z) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (x_next_2: Z) (x_data: Z) (l1_new: (@list Z)) (x_next: Z) (x_data_2: Z) (l1_new_2: (@list Z)) ,
  [| (safeExec ATrue (split_rec_rel (l1_new_2) ((cons (x_data) (l1_2))) ((cons (x_data_2) (l2_2)))) X ) |] 
  &&  [| (l1_new = (cons (x_data_2) (l1_new_2))) |] 
  &&  [| (x_next_2 <> 0) |] 
  &&  [| (l_2 = (cons (x_data) (l1_new))) |] 
  &&  [| (x <> 0) |] 
  &&  [| (q_pre_v = 0) |] 
  &&  [| (p_pre_v = 0) |]
  &&  ((p_pre) # Ptr  |-> x)
  **  (sll x (cons (x_data) (l1_2)) )
  **  ((q_pre) # Ptr  |-> x_next_2)
  **  (sll x_next_2 (cons (x_data_2) (l2_2)) )
  **  (sll x_next l1_new_2 )
  **  ((( &( "t" ) )) # Ptr  |-> x_next)
|--
  EX (q_v: Z)  (p_v: Z)  (l: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  [| (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X ) |] 
  &&  [| (q_pre_v = 0) |] 
  &&  [| (p_pre_v = 0) |]
  &&  (sll x_next l )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
  **  ((( &( "t" ) )) # Ptr  |->_)
.

Definition split_while_entail_wit_3 := 
forall (q_pre: Z) (p_pre: Z) (X: (((@list Z) * (@list Z)) -> (unit -> Prop))) (p_pre_v: Z) (q_pre_v: Z) (q_v_2: Z) (x: Z) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) ,
  [| (x_next = 0) |] 
  &&  [| (safeExec ATrue (bind ((split_rec_rel (l1_new) (l2_2) ((cons (x_data) (l1_2))))) (reversepair)) X ) |] 
  &&  [| (l_2 = (cons (x_data) (l1_new))) |] 
  &&  [| (x <> 0) |] 
  &&  [| (q_pre_v = 0) |] 
  &&  [| (p_pre_v = 0) |]
  &&  ((p_pre) # Ptr  |-> x)
  **  (sll x (cons (x_data) (l1_2)) )
  **  (sll x_next l1_new )
  **  ((q_pre) # Ptr  |-> q_v_2)
  **  (sll q_v_2 l2_2 )
  **  ((( &( "t" ) )) # Ptr  |-> x_next)
|--
  EX (q_v: Z)  (p_v: Z)  (l: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  [| (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X ) |] 
  &&  [| (q_pre_v = 0) |] 
  &&  [| (p_pre_v = 0) |]
  &&  (sll x_next l )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
  **  ((( &( "t" ) )) # Ptr  |->_)
.

Definition split_while_return_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (X: (((@list Z) * (@list Z)) -> (unit -> Prop))) (p_pre_v_2: Z) (q_pre_v_2: Z) (q_v: Z) (p_v: Z) (x: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (x = 0) |] 
  &&  [| (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X ) |] 
  &&  [| (q_pre_v_2 = 0) |] 
  &&  [| (p_pre_v_2 = 0) |]
  &&  (sll x l )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
|--
  EX (q_pre_v: Z)  (p_pre_v: Z)  (s1: (@list Z))  (s2: (@list Z)) ,
  [| (safeExec ATrue (return ((maketuple (s1) (s2)))) X ) |]
  &&  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v s1 )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v s2 )
.

Definition split_while_partial_solve_wit_1_pure := 
forall (q_pre: Z) (p_pre: Z) (X: (((@list Z) * (@list Z)) -> (unit -> Prop))) (p_pre_v: Z) (q_pre_v: Z) (q_v: Z) (p_v: Z) (x: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (x <> 0) |] 
  &&  [| (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X ) |] 
  &&  [| (q_pre_v = 0) |] 
  &&  [| (p_pre_v = 0) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
  **  ((( &( "t" ) )) # Ptr  |->_)
|--
  [| (x <> 0) |]
.

Definition split_while_partial_solve_wit_1_aux := 
forall (q_pre: Z) (p_pre: Z) (X: (((@list Z) * (@list Z)) -> (unit -> Prop))) (p_pre_v: Z) (q_pre_v: Z) (q_v: Z) (p_v: Z) (x: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (x <> 0) |] 
  &&  [| (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X ) |] 
  &&  [| (q_pre_v = 0) |] 
  &&  [| (p_pre_v = 0) |]
  &&  (sll x l )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
|--
  [| (x <> 0) |] 
  &&  [| (x <> 0) |] 
  &&  [| (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X ) |] 
  &&  [| (q_pre_v = 0) |] 
  &&  [| (p_pre_v = 0) |]
  &&  (sll x l )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
.

Definition split_while_partial_solve_wit_1 := split_while_partial_solve_wit_1_pure -> split_while_partial_solve_wit_1_aux.

Definition split_while_partial_solve_wit_2_pure := 
forall (q_pre: Z) (p_pre: Z) (X: (((@list Z) * (@list Z)) -> (unit -> Prop))) (p_pre_v: Z) (q_pre_v: Z) (q_v: Z) (p_v: Z) (x: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) ,
  [| (l = (cons (x_data) (l1_new))) |] 
  &&  [| (x <> 0) |] 
  &&  [| (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X ) |] 
  &&  [| (q_pre_v = 0) |] 
  &&  [| (p_pre_v = 0) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_next)
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> p_v)
  **  (sll x_next l1_new )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((p_pre) # Ptr  |-> x)
  **  (sll p_v l1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
  **  ((( &( "t" ) )) # Ptr  |-> x_next)
|--
  [| (safeExec ATrue (split_rec_rel ((cons (x_data) (l1_new))) (l1) (l2)) X ) |] 
  &&  [| ((cons (x_data) (l1_new)) = (cons (x_data) (l1_new))) |] 
  &&  [| (x <> 0) |] 
  &&  [| (equiv (split_rec_rel (l) (l1) (l2)) (split_rec_rel ((cons (x_data) (l1_new))) (l1) (l2)) ) |]
.

Definition split_while_partial_solve_wit_2_aux := 
forall (q_pre: Z) (p_pre: Z) (X: (((@list Z) * (@list Z)) -> (unit -> Prop))) (p_pre_v: Z) (q_pre_v: Z) (q_v: Z) (p_v: Z) (x: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) ,
  [| (l = (cons (x_data) (l1_new))) |] 
  &&  [| (x <> 0) |] 
  &&  [| (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X ) |] 
  &&  [| (q_pre_v = 0) |] 
  &&  [| (p_pre_v = 0) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> p_v)
  **  (sll x_next l1_new )
  **  ((p_pre) # Ptr  |-> x)
  **  (sll p_v l1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
|--
  [| (safeExec ATrue (split_rec_rel ((cons (x_data) (l1_new))) (l1) (l2)) X ) |] 
  &&  [| ((cons (x_data) (l1_new)) = (cons (x_data) (l1_new))) |] 
  &&  [| (x <> 0) |] 
  &&  [| (equiv (split_rec_rel (l) (l1) (l2)) (split_rec_rel ((cons (x_data) (l1_new))) (l1) (l2)) ) |] 
  &&  [| (l = (cons (x_data) (l1_new))) |] 
  &&  [| (x <> 0) |] 
  &&  [| (q_pre_v = 0) |] 
  &&  [| (p_pre_v = 0) |]
  &&  ((p_pre) # Ptr  |-> x)
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> p_v)
  **  (sll p_v l1 )
  **  (sll x_next l1_new )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
.

Definition split_while_partial_solve_wit_2 := split_while_partial_solve_wit_2_pure -> split_while_partial_solve_wit_2_aux.

Definition split_while_partial_solve_wit_3_pure := 
forall (q_pre: Z) (p_pre: Z) (X: (((@list Z) * (@list Z)) -> (unit -> Prop))) (p_pre_v: Z) (q_pre_v: Z) (q_v: Z) (x: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) ,
  [| (x_next <> 0) |] 
  &&  [| (safeExec ATrue (bind ((split_rec_rel (l1_new) (l2) ((cons (x_data) (l1))))) (reversepair)) X ) |] 
  &&  [| (l = (cons (x_data) (l1_new))) |] 
  &&  [| (x <> 0) |] 
  &&  [| (q_pre_v = 0) |] 
  &&  [| (p_pre_v = 0) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> x)
  **  (sll x (cons (x_data) (l1)) )
  **  ((( &( "x" ) )) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
  **  ((( &( "t" ) )) # Ptr  |-> x_next)
|--
  [| (x_next <> 0) |]
.

Definition split_while_partial_solve_wit_3_aux := 
forall (q_pre: Z) (p_pre: Z) (X: (((@list Z) * (@list Z)) -> (unit -> Prop))) (p_pre_v: Z) (q_pre_v: Z) (q_v: Z) (x: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) ,
  [| (x_next <> 0) |] 
  &&  [| (safeExec ATrue (bind ((split_rec_rel (l1_new) (l2) ((cons (x_data) (l1))))) (reversepair)) X ) |] 
  &&  [| (l = (cons (x_data) (l1_new))) |] 
  &&  [| (x <> 0) |] 
  &&  [| (q_pre_v = 0) |] 
  &&  [| (p_pre_v = 0) |]
  &&  ((p_pre) # Ptr  |-> x)
  **  (sll x (cons (x_data) (l1)) )
  **  (sll x_next l1_new )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
|--
  EX (y: Z) ,
  [| (x_next <> 0) |] 
  &&  [| (x_next <> 0) |] 
  &&  [| (safeExec ATrue (bind ((split_rec_rel (l1_new) (l2) ((cons (x_data) (l1))))) (reversepair)) X ) |] 
  &&  [| (l = (cons (x_data) (l1_new))) |] 
  &&  [| (x <> 0) |] 
  &&  [| (q_pre_v = 0) |] 
  &&  [| (p_pre_v = 0) |]
  &&  (sll x_next l1_new )
  **  (sll y l1 )
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((p_pre) # Ptr  |-> x)
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
.

Definition split_while_partial_solve_wit_3 := split_while_partial_solve_wit_3_pure -> split_while_partial_solve_wit_3_aux.

Definition split_while_partial_solve_wit_4_pure := 
forall (q_pre: Z) (p_pre: Z) (X: (((@list Z) * (@list Z)) -> (unit -> Prop))) (p_pre_v: Z) (q_pre_v: Z) (q_v: Z) (x: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) (y: Z) (x_next_2: Z) (x_data_2: Z) (l1_new_2: (@list Z)) ,
  [| (l1_new = (cons (x_data_2) (l1_new_2))) |] 
  &&  [| (x_next <> 0) |] 
  &&  [| (safeExec ATrue (bind ((split_rec_rel (l1_new) (l2) ((cons (x_data) (l1))))) (reversepair)) X ) |] 
  &&  [| (l = (cons (x_data) (l1_new))) |] 
  &&  [| (x <> 0) |] 
  &&  [| (q_pre_v = 0) |] 
  &&  [| (p_pre_v = 0) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_next_2)
  **  ((&((x_next)  # "list" ->ₛ "data")) # Int  |-> x_data_2)
  **  ((&((x_next)  # "list" ->ₛ "next")) # Ptr  |-> q_v)
  **  (sll x_next_2 l1_new_2 )
  **  (sll y l1 )
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> x)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((q_pre) # Ptr  |-> x_next)
  **  (sll q_v l2 )
  **  ((( &( "t" ) )) # Ptr  |-> x_next_2)
|--
  [| (safeExec ATrue (bind ((split_rec_rel ((cons (x_data_2) (l1_new_2))) (l2) ((cons (x_data) (l1))))) (reversepair)) X ) |] 
  &&  [| ((cons (x_data_2) (l1_new_2)) = (cons (x_data_2) (l1_new_2))) |] 
  &&  [| (x_next <> 0) |] 
  &&  [| (equiv (split_rec_rel (l1_new) (l2) ((cons (x_data) (l1)))) (split_rec_rel ((cons (x_data_2) (l1_new_2))) (l2) ((cons (x_data) (l1)))) ) |] 
  &&  [| (equiv reversepair reversepair ) |]
.

Definition split_while_partial_solve_wit_4_aux := 
forall (q_pre: Z) (p_pre: Z) (X: (((@list Z) * (@list Z)) -> (unit -> Prop))) (p_pre_v: Z) (q_pre_v: Z) (q_v: Z) (x: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) (y: Z) (x_next_2: Z) (x_data_2: Z) (l1_new_2: (@list Z)) ,
  [| (l1_new = (cons (x_data_2) (l1_new_2))) |] 
  &&  [| (x_next <> 0) |] 
  &&  [| (safeExec ATrue (bind ((split_rec_rel (l1_new) (l2) ((cons (x_data) (l1))))) (reversepair)) X ) |] 
  &&  [| (l = (cons (x_data) (l1_new))) |] 
  &&  [| (x <> 0) |] 
  &&  [| (q_pre_v = 0) |] 
  &&  [| (p_pre_v = 0) |]
  &&  ((&((x_next)  # "list" ->ₛ "data")) # Int  |-> x_data_2)
  **  ((&((x_next)  # "list" ->ₛ "next")) # Ptr  |-> q_v)
  **  (sll x_next_2 l1_new_2 )
  **  (sll y l1 )
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((p_pre) # Ptr  |-> x)
  **  ((q_pre) # Ptr  |-> x_next)
  **  (sll q_v l2 )
|--
  [| (safeExec ATrue (bind ((split_rec_rel ((cons (x_data_2) (l1_new_2))) (l2) ((cons (x_data) (l1))))) (reversepair)) X ) |] 
  &&  [| ((cons (x_data_2) (l1_new_2)) = (cons (x_data_2) (l1_new_2))) |] 
  &&  [| (x_next <> 0) |] 
  &&  [| (equiv (split_rec_rel (l1_new) (l2) ((cons (x_data) (l1)))) (split_rec_rel ((cons (x_data_2) (l1_new_2))) (l2) ((cons (x_data) (l1)))) ) |] 
  &&  [| (equiv reversepair reversepair ) |] 
  &&  [| (l1_new = (cons (x_data_2) (l1_new_2))) |] 
  &&  [| (x_next <> 0) |] 
  &&  [| (l = (cons (x_data) (l1_new))) |] 
  &&  [| (x <> 0) |] 
  &&  [| (q_pre_v = 0) |] 
  &&  [| (p_pre_v = 0) |]
  &&  ((q_pre) # Ptr  |-> x_next)
  **  ((&((x_next)  # "list" ->ₛ "data")) # Int  |-> x_data_2)
  **  ((&((x_next)  # "list" ->ₛ "next")) # Ptr  |-> q_v)
  **  (sll q_v l2 )
  **  (sll x_next_2 l1_new_2 )
  **  ((p_pre) # Ptr  |-> x)
  **  (sll x (cons (x_data) (l1)) )
.

Definition split_while_partial_solve_wit_4 := split_while_partial_solve_wit_4_pure -> split_while_partial_solve_wit_4_aux.

Definition split_while_which_implies_wit_1 := 
forall (l1: (@list Z)) (x: Z) ,
  [| (x <> 0) |]
  &&  (sll x l1 )
|--
  EX (x_next: Z)  (x_data: Z)  (l1_new: (@list Z)) ,
  [| (l1 = (cons (x_data) (l1_new))) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
.

Definition split_while_which_implies_wit_2 := 
forall (X: (((@list Z) * (@list Z)) -> (unit -> Prop))) (x_data: Z) (l_new: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (l: (@list Z)) (p: Z) (p_v: Z) (p_v_next: Z) (x: Z) (q: Z) (q_v: Z) ,
  [| (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X ) |] 
  &&  [| (l = (cons (x_data) (l_new))) |] 
  &&  [| (p_v <> 0) |]
  &&  ((p) # Ptr  |-> p_v)
  **  ((&((p_v)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((p_v)  # "list" ->ₛ "next")) # Ptr  |-> p_v_next)
  **  (sll p_v_next l1 )
  **  (sll x l_new )
  **  ((q) # Ptr  |-> q_v)
  **  (sll q_v l2 )
|--
  [| (safeExec ATrue (bind ((split_rec_rel (l_new) (l2) ((cons (x_data) (l1))))) (reversepair)) X ) |]
  &&  ((p) # Ptr  |-> p_v)
  **  (sll p_v (cons (x_data) (l1)) )
  **  (sll x l_new )
  **  ((q) # Ptr  |-> q_v)
  **  (sll q_v l2 )
.

Definition split_while_which_implies_wit_3 := 
forall (l1: (@list Z)) (x: Z) ,
  [| (x <> 0) |]
  &&  (sll x l1 )
|--
  EX (x_next: Z)  (x_data: Z)  (l1_new: (@list Z)) ,
  [| (l1 = (cons (x_data) (l1_new))) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
.

Definition split_while_which_implies_wit_4 := 
forall (X: (((@list Z) * (@list Z)) -> (unit -> Prop))) (x_data2: Z) (x_data: Z) (l_new: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (l: (@list Z)) (q: Z) (q_v: Z) (q_v_next: Z) (x: Z) (p: Z) (p_v: Z) ,
  [| (safeExec ATrue (bind ((split_rec_rel (l) (l2) ((cons (x_data) (l1))))) (reversepair)) X ) |] 
  &&  [| (l = (cons (x_data2) (l_new))) |] 
  &&  [| (q_v <> 0) |]
  &&  ((q) # Ptr  |-> q_v)
  **  ((&((q_v)  # "list" ->ₛ "data")) # Int  |-> x_data2)
  **  ((&((q_v)  # "list" ->ₛ "next")) # Ptr  |-> q_v_next)
  **  (sll q_v_next l2 )
  **  (sll x l_new )
  **  ((p) # Ptr  |-> p_v)
  **  (sll p_v (cons (x_data) (l1)) )
|--
  [| (safeExec ATrue (split_rec_rel (l_new) ((cons (x_data) (l1))) ((cons (x_data2) (l2)))) X ) |]
  &&  ((p) # Ptr  |-> p_v)
  **  (sll p_v (cons (x_data) (l1)) )
  **  ((q) # Ptr  |-> q_v)
  **  (sll q_v (cons (x_data2) (l2)) )
  **  (sll x l_new )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include sll_Strategy_Correct.
Include safeexec_Strategy_Correct.

Axiom proof_of_split_while_safety_wit_1 : split_while_safety_wit_1.
Axiom proof_of_split_while_safety_wit_2 : split_while_safety_wit_2.
Axiom proof_of_split_while_entail_wit_1 : split_while_entail_wit_1.
Axiom proof_of_split_while_entail_wit_2 : split_while_entail_wit_2.
Axiom proof_of_split_while_entail_wit_3 : split_while_entail_wit_3.
Axiom proof_of_split_while_return_wit_1 : split_while_return_wit_1.
Axiom proof_of_split_while_partial_solve_wit_1_pure : split_while_partial_solve_wit_1_pure.
Axiom proof_of_split_while_partial_solve_wit_1 : split_while_partial_solve_wit_1.
Axiom proof_of_split_while_partial_solve_wit_2_pure : split_while_partial_solve_wit_2_pure.
Axiom proof_of_split_while_partial_solve_wit_2 : split_while_partial_solve_wit_2.
Axiom proof_of_split_while_partial_solve_wit_3_pure : split_while_partial_solve_wit_3_pure.
Axiom proof_of_split_while_partial_solve_wit_3 : split_while_partial_solve_wit_3.
Axiom proof_of_split_while_partial_solve_wit_4_pure : split_while_partial_solve_wit_4_pure.
Axiom proof_of_split_while_partial_solve_wit_4 : split_while_partial_solve_wit_4.
Axiom proof_of_split_while_which_implies_wit_1 : split_while_which_implies_wit_1.
Axiom proof_of_split_while_which_implies_wit_2 : split_while_which_implies_wit_2.
Axiom proof_of_split_while_which_implies_wit_3 : split_while_which_implies_wit_3.
Axiom proof_of_split_while_which_implies_wit_4 : split_while_which_implies_wit_4.

End VC_Correct.
