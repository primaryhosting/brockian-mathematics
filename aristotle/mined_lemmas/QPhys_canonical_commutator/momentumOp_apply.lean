/-
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 does not allow a
-- module docstring to precede `import`; the exact docstring is repeated below.)

import Mathlib

/-!
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace QPhys

open SchwartzMap

/-- The function `x ↦ (x : ℂ)` has temperate growth (it is a continuous linear map). -/

theorem momentumOp_apply (ℏ : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    momentumOp ℏ f x = -(Complex.I * (ℏ : ℂ)) * deriv (⇑f) x := by
  simp [momentumOp, smul_eq_mul]

/-- The derivative of `x ↦ x * f x` for a Schwartz function `f`. -/
