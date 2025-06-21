Require Import thm_apply_goal thm_apply_proof_auto thm_apply_proof_manual.

Module VC_Correctness : VC_Correct.
  Include thm_apply_proof_auto.
  Include thm_apply_proof_manual.
End VC_Correctness.
