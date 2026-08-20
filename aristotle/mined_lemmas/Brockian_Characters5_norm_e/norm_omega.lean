/-
# Norm E
Category: Characters
Target: Brockian.Characters5.norm_e
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Norm E
Category: Characters
Target: Brockian.Characters5.norm_e
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Brockian
namespace Characters5

/-- The primitive fifth root of unity `ω = exp(2πi/5)`. -/

theorem norm_omega : ‖omega‖ = 1 := by
  have h : (2 * (Real.pi : ℂ) * Complex.I / 5) = ((2 * Real.pi / 5 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [omega, h, Complex.norm_exp_ofReal_mul_I]

/-- The additive character has unit modulus. -/
