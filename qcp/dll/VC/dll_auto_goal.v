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
Require Import dll_shape_lib.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import dll_shape_strategy_goal.
From SimpleC.EE Require Import dll_shape_strategy_proof.

(*----- Function dll_copy -----*)

Definition dll_copy_safety_wit_1 := 
forall (x_pre: Z) ,
  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (dlistrep_shape x_pre 0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition dll_copy_safety_wit_2 := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (t_prev: Z) (p_prev: Z) (p: Z) (t_data: Z) (t_next: Z) (t: Z) (x: Z) (y_2: Z) ,
  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y_2 p )
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (dllseg_shape x_pre 0 p_prev p )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (dllseg_shape y 0 t_prev t )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition dll_copy_entail_wit_1 := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> retval_prev)
  **  (dlistrep_shape x_pre 0 )
|--
  EX (t_prev: Z)  (p_prev: Z)  (t_data: Z)  (t_next: Z) ,
  [| (retval <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  (dllseg_shape x_pre 0 p_prev x_pre )
  **  (dlistrep_shape x_pre p_prev )
  **  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape retval 0 t_prev retval )
.

Definition dll_copy_entail_wit_2 := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (t_prev_2: Z) (p_prev_2: Z) (p: Z) (t_data_2: Z) (t_next_2: Z) (t: Z) (x: Z) (y_2: Z) (retval_prev_2: Z) (retval_next_2: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_next_2 = 0) |] 
  &&  [| (retval_prev_2 = 0) |] 
  &&  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next_2 = 0) |] 
  &&  [| (t_data_2 = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((retval_2)  # "list" ->ₛ "data")) # Int  |-> 0)
  **  ((&((retval_2)  # "list" ->ₛ "next")) # Ptr  |-> retval_next_2)
  **  ((&((retval_2)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y_2 p )
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev_2)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> retval_2)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dllseg_shape x_pre 0 p_prev_2 p )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev_2)
  **  (dllseg_shape y 0 t_prev_2 t )
|--
  EX (t_prev: Z)  (p_prev: Z)  (t_data: Z)  (t_next: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((retval_2)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((retval_2)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  (dllseg_shape x_pre 0 p_prev y_2 )
  **  (dlistrep_shape y_2 p_prev )
  **  ((&((retval_2)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape y 0 t_prev retval_2 )
.

Definition dll_copy_return_wit_1 := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (t_prev: Z) (p_prev: Z) (p: Z) (t_data: Z) (t_next: Z) (t: Z) ,
  [| (p = 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  (dllseg_shape x_pre 0 p_prev p )
  **  (dlistrep_shape p p_prev )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape y 0 t_prev t )
|--
  (dlistrep_shape y 0 )
  **  (dlistrep_shape x_pre 0 )
.

Definition dll_copy_partial_solve_wit_1_pure := 
forall (x_pre: Z) ,
  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (dlistrep_shape x_pre 0 )
|--
  [| (0 = 0) |]
.

Definition dll_copy_partial_solve_wit_1_aux := 
forall (x_pre: Z) ,
  (dlistrep_shape x_pre 0 )
|--
  [| (0 = 0) |]
  &&  (dlistrep_shape x_pre 0 )
.

Definition dll_copy_partial_solve_wit_1 := dll_copy_partial_solve_wit_1_pure -> dll_copy_partial_solve_wit_1_aux.

Definition dll_copy_partial_solve_wit_2 := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y_2: Z) (t_prev: Z) (p_prev: Z) (p: Z) (t_data: Z) (t_next: Z) (t: Z) ,
  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  (dllseg_shape x_pre 0 p_prev p )
  **  (dlistrep_shape p p_prev )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape y_2 0 t_prev t )
|--
  EX (y: Z)  (x: Z) ,
  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y p )
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> t_data)
  **  (dllseg_shape x_pre 0 p_prev p )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape y_2 0 t_prev t )
.

Definition dll_copy_partial_solve_wit_3_pure := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (t_prev: Z) (p_prev: Z) (p: Z) (t_data: Z) (t_next: Z) (t: Z) (x: Z) (y_2: Z) ,
  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y_2 p )
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (dllseg_shape x_pre 0 p_prev p )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (dllseg_shape y 0 t_prev t )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  [| (0 = 0) |]
.

Definition dll_copy_partial_solve_wit_3_aux := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (t_prev: Z) (p_prev: Z) (p: Z) (t_data: Z) (t_next: Z) (t: Z) (x: Z) (y_2: Z) ,
  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y_2 p )
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dllseg_shape x_pre 0 p_prev p )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape y 0 t_prev t )
|--
  [| (0 = 0) |] 
  &&  [| (p <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (t_next = 0) |] 
  &&  [| (t_data = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_next = 0) |] 
  &&  [| (retval_prev = 0) |]
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y_2 p )
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dllseg_shape x_pre 0 p_prev p )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape y 0 t_prev t )
.

Definition dll_copy_partial_solve_wit_3 := dll_copy_partial_solve_wit_3_pure -> dll_copy_partial_solve_wit_3_aux.

(*----- Function dll_free -----*)

Definition dll_free_entail_wit_1 := 
forall (x_pre: Z) ,
  (dlistrep_shape x_pre 0 )
|--
  EX (prev: Z) ,
  (dlistrep_shape x_pre prev )
.

Definition dll_free_entail_wit_2 := 
forall (x: Z) (y: Z) ,
  [| (x <> 0) |]
  &&  (dlistrep_shape y x )
  **  ((( &( "y" ) )) # Ptr  |-> y)
|--
  EX (prev: Z) ,
  (dlistrep_shape y prev )
  **  ((( &( "y" ) )) # Ptr  |->_)
.

Definition dll_free_return_wit_1 := 
forall (x: Z) (prev: Z) ,
  [| (x = 0) |]
  &&  (dlistrep_shape x prev )
|--
  TT && emp 
.

Definition dll_free_partial_solve_wit_1 := 
forall (x_2: Z) (prev: Z) ,
  [| (x_2 <> 0) |]
  &&  (dlistrep_shape x_2 prev )
|--
  EX (y: Z)  (x: Z) ,
  [| (x_2 <> 0) |]
  &&  ((&((x_2)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y x_2 )
  **  ((&((x_2)  # "list" ->ₛ "prev")) # Ptr  |-> prev)
  **  ((&((x_2)  # "list" ->ₛ "data")) # Int  |-> x)
.

Definition dll_free_partial_solve_wit_2 := 
forall (x: Z) (prev: Z) (x_2: Z) (y: Z) ,
  [| (x <> 0) |]
  &&  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y x )
  **  ((&((x)  # "list" ->ₛ "prev")) # Ptr  |-> prev)
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_2)
|--
  [| (x <> 0) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((x)  # "list" ->ₛ "prev")) # Ptr  |-> prev)
  **  (dlistrep_shape y x )
.

(*----- Function reverse -----*)

Definition reverse_safety_wit_1 := 
forall (p_pre: Z) ,
  ((( &( "v" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (dlistrep_shape p_pre 0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition reverse_entail_wit_1 := 
forall (p_pre: Z) ,
  (dlistrep_shape p_pre 0 )
|--
  (dlistrep_shape 0 p_pre )
  **  (dlistrep_shape p_pre 0 )
.

Definition reverse_entail_wit_2 := 
forall (w: Z) (v: Z) (x: Z) (y: Z) ,
  [| (v <> 0) |]
  &&  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> w)
  **  (dlistrep_shape y v )
  **  ((&((v)  # "list" ->ₛ "prev")) # Ptr  |-> y)
  **  ((&((v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape w v )
  **  ((( &( "t" ) )) # Ptr  |-> y)
|--
  (dlistrep_shape v y )
  **  (dlistrep_shape y v )
  **  ((( &( "t" ) )) # Ptr  |->_)
.

Definition reverse_return_wit_1 := 
forall (w: Z) (v: Z) ,
  [| (v = 0) |]
  &&  (dlistrep_shape w v )
  **  (dlistrep_shape v w )
|--
  (dlistrep_shape w 0 )
.

Definition reverse_partial_solve_wit_1 := 
forall (w: Z) (v: Z) ,
  [| (v <> 0) |]
  &&  (dlistrep_shape w v )
  **  (dlistrep_shape v w )
|--
  EX (y: Z)  (x: Z) ,
  [| (v <> 0) |]
  &&  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y v )
  **  ((&((v)  # "list" ->ₛ "prev")) # Ptr  |-> w)
  **  ((&((v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape w v )
.

(*----- Function append -----*)

Definition append_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  ((( &( "u" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (dlistrep_shape x_pre 0 )
  **  (dlistrep_shape y_pre 0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition append_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (x: Z) (y: Z) ,
  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y x_pre )
  **  ((&((x_pre)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y_pre 0 )
|--
  EX (t_prev: Z)  (t_next: Z)  (v: Z) ,
  [| (y = t_next) |] 
  &&  [| (x_pre <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep_shape y x_pre )
  **  ((&((x_pre)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev x_pre )
  **  (dlistrep_shape y_pre 0 )
.

Definition append_entail_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (t_prev_2: Z) (t_next_2: Z) (u: Z) (v_2: Z) (t: Z) (x: Z) (y: Z) ,
  [| (u <> 0) |] 
  &&  [| (u = t_next_2) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y u )
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next_2)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev_2)
  **  (dllseg_shape x_pre 0 t_prev_2 t )
  **  (dlistrep_shape y_pre 0 )
|--
  EX (t_prev: Z)  (t_next: Z)  (v: Z) ,
  [| (y = t_next) |] 
  &&  [| (u <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep_shape y u )
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev u )
  **  (dlistrep_shape y_pre 0 )
.

Definition append_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre = 0) |]
  &&  (dlistrep_shape x_pre 0 )
  **  (dlistrep_shape y_pre 0 )
|--
  (dlistrep_shape y_pre 0 )
.

Definition append_return_wit_2_1 := 
forall (y_pre: Z) (x_pre: Z) (t_prev: Z) (t_next: Z) (u: Z) (v: Z) (t: Z) ,
  [| (y_pre = 0) |] 
  &&  [| (u = 0) |] 
  &&  [| (u = t_next) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y_pre)
  **  (dlistrep_shape u t )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
  **  (dlistrep_shape y_pre 0 )
|--
  (dlistrep_shape x_pre 0 )
.

Definition append_return_wit_2_2 := 
forall (y_pre: Z) (x_pre: Z) (t_prev: Z) (t_next: Z) (u: Z) (v: Z) (t: Z) (x: Z) (y: Z) ,
  [| (y_pre <> 0) |] 
  &&  [| (u = 0) |] 
  &&  [| (u = t_next) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((y_pre)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  (dlistrep_shape y y_pre )
  **  ((&((y_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((y_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y_pre)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
|--
  (dlistrep_shape x_pre 0 )
.

Definition append_partial_solve_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (x_pre <> 0) |]
  &&  (dlistrep_shape x_pre 0 )
  **  (dlistrep_shape y_pre 0 )
|--
  EX (y: Z)  (x: Z) ,
  [| (x_pre <> 0) |]
  &&  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y x_pre )
  **  ((&((x_pre)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y_pre 0 )
.

Definition append_partial_solve_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (t_prev: Z) (t_next: Z) (u: Z) (v: Z) (t: Z) ,
  [| (u <> 0) |] 
  &&  [| (u = t_next) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep_shape u t )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
  **  (dlistrep_shape y_pre 0 )
|--
  EX (y: Z)  (x: Z) ,
  [| (u <> 0) |] 
  &&  [| (u = t_next) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y u )
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
  **  (dlistrep_shape y_pre 0 )
.

Definition append_partial_solve_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (t_prev: Z) (t_next: Z) (u: Z) (v: Z) (t: Z) ,
  [| (y_pre <> 0) |] 
  &&  [| (u = 0) |] 
  &&  [| (u = t_next) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y_pre)
  **  (dlistrep_shape u t )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
  **  (dlistrep_shape y_pre 0 )
|--
  EX (y: Z)  (x: Z) ,
  [| (y_pre <> 0) |] 
  &&  [| (u = 0) |] 
  &&  [| (u = t_next) |] 
  &&  [| (t <> 0) |] 
  &&  [| (x_pre <> 0) |]
  &&  ((&((y_pre)  # "list" ->ₛ "prev")) # Ptr  |->_)
  **  (dlistrep_shape y y_pre )
  **  ((&((y_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((y_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y_pre)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
.

(*----- Function iter -----*)

Definition iter_entail_wit_1 := 
forall (l_pre: Z) ,
  (dlistrep_shape l_pre 0 )
|--
  EX (p_prev: Z) ,
  (dllseg_shape l_pre 0 p_prev l_pre )
  **  (dlistrep_shape l_pre p_prev )
.

Definition iter_entail_wit_2 := 
forall (l_pre: Z) (p_prev_2: Z) (p: Z) (x: Z) (y: Z) ,
  [| (p <> 0) |]
  &&  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y p )
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev_2)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dllseg_shape l_pre 0 p_prev_2 p )
|--
  EX (p_prev: Z) ,
  (dllseg_shape l_pre 0 p_prev y )
  **  (dlistrep_shape y p_prev )
.

Definition iter_return_wit_1 := 
forall (l_pre: Z) (p_prev: Z) (p: Z) ,
  [| (p = 0) |]
  &&  (dllseg_shape l_pre 0 p_prev p )
  **  (dlistrep_shape p p_prev )
|--
  (dlistrep_shape l_pre 0 )
.

Definition iter_partial_solve_wit_1 := 
forall (l_pre: Z) (p_prev: Z) (p: Z) ,
  [| (p <> 0) |]
  &&  (dllseg_shape l_pre 0 p_prev p )
  **  (dlistrep_shape p p_prev )
|--
  EX (y: Z)  (x: Z) ,
  [| (p <> 0) |]
  &&  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y p )
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dllseg_shape l_pre 0 p_prev p )
.

(*----- Function iter_back -----*)

Definition iter_back_safety_wit_1 := 
forall (head_pre: Z) (l_pre: Z) (l_prev: Z) ,
  [| (head_pre <> 0) |]
  &&  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (dllseg_shape head_pre 0 l_prev l_pre )
  **  (dlistrep_shape l_pre l_prev )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition iter_back_entail_wit_1 := 
forall (head_pre: Z) (l_pre: Z) (l_prev: Z) ,
  [| (l_pre <> 0) |] 
  &&  [| (head_pre <> 0) |]
  &&  (dllseg_shape head_pre 0 l_prev l_pre )
  **  (dlistrep_shape l_pre l_prev )
|--
  EX (p_next: Z)  (p_prev: Z)  (v: Z) ,
  [| (l_pre <> 0) |] 
  &&  [| (l_pre <> 0) |] 
  &&  [| (head_pre <> 0) |]
  &&  ((&((l_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((l_pre)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  (dllseg_shape head_pre 0 p_prev l_pre )
  **  ((&((l_pre)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (dlistrep_shape p_next l_pre )
.

Definition iter_back_entail_wit_2 := 
forall (head_pre: Z) (l_pre: Z) (p_next_2: Z) (p_prev_2: Z) (v_2: Z) (p: Z) ,
  [| (p <> head_pre) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l_pre <> 0) |] 
  &&  [| (head_pre <> 0) |]
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev_2)
  **  (dllseg_shape head_pre 0 p_prev_2 p )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next_2)
  **  (dlistrep_shape p_next_2 p )
|--
  EX (p_next: Z)  (p_prev: Z)  (v: Z) ,
  [| (p_prev_2 <> 0) |] 
  &&  [| (l_pre <> 0) |] 
  &&  [| (head_pre <> 0) |]
  &&  ((&((p_prev_2)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((p_prev_2)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  (dllseg_shape head_pre 0 p_prev p_prev_2 )
  **  ((&((p_prev_2)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (dlistrep_shape p_next p_prev_2 )
.

Definition iter_back_return_wit_1 := 
forall (head_pre: Z) (l_pre: Z) (l_prev: Z) ,
  [| (l_pre = 0) |] 
  &&  [| (head_pre <> 0) |]
  &&  (dllseg_shape head_pre 0 l_prev l_pre )
  **  (dlistrep_shape l_pre l_prev )
|--
  (dlistrep_shape head_pre 0 )
.

Definition iter_back_return_wit_2 := 
forall (head_pre: Z) (l_pre: Z) (p_next: Z) (p_prev: Z) (v: Z) (p: Z) ,
  [| (p = head_pre) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l_pre <> 0) |] 
  &&  [| (head_pre <> 0) |]
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  (dllseg_shape head_pre 0 p_prev p )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (dlistrep_shape p_next p )
|--
  (dlistrep_shape p 0 )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include dll_shape_Strategy_Correct.

Axiom proof_of_dll_copy_safety_wit_1 : dll_copy_safety_wit_1.
Axiom proof_of_dll_copy_safety_wit_2 : dll_copy_safety_wit_2.
Axiom proof_of_dll_copy_entail_wit_1 : dll_copy_entail_wit_1.
Axiom proof_of_dll_copy_entail_wit_2 : dll_copy_entail_wit_2.
Axiom proof_of_dll_copy_return_wit_1 : dll_copy_return_wit_1.
Axiom proof_of_dll_copy_partial_solve_wit_1_pure : dll_copy_partial_solve_wit_1_pure.
Axiom proof_of_dll_copy_partial_solve_wit_1 : dll_copy_partial_solve_wit_1.
Axiom proof_of_dll_copy_partial_solve_wit_2 : dll_copy_partial_solve_wit_2.
Axiom proof_of_dll_copy_partial_solve_wit_3_pure : dll_copy_partial_solve_wit_3_pure.
Axiom proof_of_dll_copy_partial_solve_wit_3 : dll_copy_partial_solve_wit_3.
Axiom proof_of_dll_free_entail_wit_1 : dll_free_entail_wit_1.
Axiom proof_of_dll_free_entail_wit_2 : dll_free_entail_wit_2.
Axiom proof_of_dll_free_return_wit_1 : dll_free_return_wit_1.
Axiom proof_of_dll_free_partial_solve_wit_1 : dll_free_partial_solve_wit_1.
Axiom proof_of_dll_free_partial_solve_wit_2 : dll_free_partial_solve_wit_2.
Axiom proof_of_reverse_safety_wit_1 : reverse_safety_wit_1.
Axiom proof_of_reverse_entail_wit_1 : reverse_entail_wit_1.
Axiom proof_of_reverse_entail_wit_2 : reverse_entail_wit_2.
Axiom proof_of_reverse_return_wit_1 : reverse_return_wit_1.
Axiom proof_of_reverse_partial_solve_wit_1 : reverse_partial_solve_wit_1.
Axiom proof_of_append_safety_wit_1 : append_safety_wit_1.
Axiom proof_of_append_entail_wit_1 : append_entail_wit_1.
Axiom proof_of_append_entail_wit_2 : append_entail_wit_2.
Axiom proof_of_append_return_wit_1 : append_return_wit_1.
Axiom proof_of_append_return_wit_2_1 : append_return_wit_2_1.
Axiom proof_of_append_return_wit_2_2 : append_return_wit_2_2.
Axiom proof_of_append_partial_solve_wit_1 : append_partial_solve_wit_1.
Axiom proof_of_append_partial_solve_wit_2 : append_partial_solve_wit_2.
Axiom proof_of_append_partial_solve_wit_3 : append_partial_solve_wit_3.
Axiom proof_of_iter_entail_wit_1 : iter_entail_wit_1.
Axiom proof_of_iter_entail_wit_2 : iter_entail_wit_2.
Axiom proof_of_iter_return_wit_1 : iter_return_wit_1.
Axiom proof_of_iter_partial_solve_wit_1 : iter_partial_solve_wit_1.
Axiom proof_of_iter_back_safety_wit_1 : iter_back_safety_wit_1.
Axiom proof_of_iter_back_entail_wit_1 : iter_back_entail_wit_1.
Axiom proof_of_iter_back_entail_wit_2 : iter_back_entail_wit_2.
Axiom proof_of_iter_back_return_wit_1 : iter_back_return_wit_1.
Axiom proof_of_iter_back_return_wit_2 : iter_back_return_wit_2.

End VC_Correct.
