import RecognitionScience

namespace PvsNP.RSFoundation

open RecognitionScience

/-- Re-export the principal definitions and theorems from the external
`RecognitionScience` library so that legacy code referring to
`PvsNP.RSFoundation.*` continues to compile.  No new axioms or proofs are
introduced here. -/
export RecognitionScience (φ φ_property φ_gt_one
  E_coh E_coh_lt_one E_coh_pos
  τ₀ l_P
  RS_correction RS_correction_unbounded
  information_lower_bound recognition_lower_bound
  ca_state_count ca_state_count_eq
  DualComplexity classical_assumption)

end PvsNP.RSFoundation
