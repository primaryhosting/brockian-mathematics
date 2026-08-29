/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Real MeasureTheory
open scoped Topology BigOperators Classical

namespace Math2

/-! ## The Sato–Tate distribution -/

/-- The Sato–Tate density `(2/π) sin²θ` on `[0, π]`. -/

lemma continuous_of_mem_USpan {g : ℝ → ℝ} (hg : g ∈ USpan) : Continuous g := by
  induction hg using Submodule.span_induction with
  | mem g hg => obtain ⟨k, rfl⟩ := hg; exact continuous_UBasis k
  | zero => exact continuous_const
  | add g h _ _ ih1 ih2 => exact ih1.add ih2
  | smul c g _ ih => exact ih.const_smul c

/-! ## The averaging law -/

/-- The empirical average of `f` over the angles attached to the primes below `X`. -/
