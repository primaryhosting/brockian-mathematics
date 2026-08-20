/-
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Statement: State the Bekenstein bound S ≤ 2πkRE/ℏc.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Note: Lean 4 requires `import` to be the first command in a file, so this header is written as a
plain block comment `/- ... -/` rather than a module docstring `/-! ... -/`; the text is otherwise
exactly as specified.
-/

import Mathlib

open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Phys

/-- The Bekenstein bound `2 π k R E / (ℏ c)` on the entropy of a system of energy `E`
contained in a sphere of radius `R`. -/

theorem bekenstein_bound_sharp {k hbar c G M R E : ℝ} (hG : G ≠ 0) (hM : M ≠ 0) :
    ∃ S : ℝ, S = deriv (bhEntropy k hbar c G) M * deliveredMass G M R E ∧
      S = bekensteinBound k hbar c R E := by
  refine ⟨deriv (bhEntropy k hbar c G) M * deliveredMass G M R E, rfl, ?_⟩
  rw [deriv_bhEntropy]
  unfold deliveredMass bekensteinBound
  field_simp
  ring

end Phys

