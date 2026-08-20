/-
# Norm E
Category: Characters
Target: Brockian.Characters5.norm_e
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity, `ω = exp(2πi/5)`. -/

theorem norm_omega : ‖omega‖ = 1 := by
  have h : (2 * (Real.pi : ℂ) * Complex.I / 5) = ((2 * Real.pi / 5 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [omega, h, Complex.norm_exp_ofReal_mul_I]

/-- The additive character has unit modulus: `‖e k‖ = 1` for every `k : ZMod 5`. -/
