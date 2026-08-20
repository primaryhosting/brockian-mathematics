/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Matrix

namespace Phys

/-! ## Complexified Minkowski space and the complex Lorentz group -/

/-- Real Minkowski space `ℝ^{1,3}`. -/
abbrev Spacetime := Fin 4 → ℝ

/-- Complexified Minkowski space `ℂ^4`, the domain of the analytically continued
Wightman functions. -/
abbrev CSpace := Fin 4 → ℂ

/-- The Minkowski bilinear form on real Minkowski space (signature `+ - - -`). -/

theorem inversion_invariance (T : WightmanTheory) (n : ℕ) (z : Fin n → CSpace) :
    (T.W n fun i => -z i) = T.W n z := by
  have key : (fun i => -z i) = fun i => inversionPath 1 *ᵥ z i := by
    funext i
    rw [inversionPath_one, Matrix.neg_mulVec, Matrix.one_mulVec]
  rw [key]
  exact T.bhw_covariance inversionPath inversionPath_continuous inversionPath_zero
    inversionPath_lorentz n z

/-- **CPT theorem.**  For any Lorentz-invariant local quantum field theory (in the Wightman
sense), the Wightman functions are invariant under the CPT transformation, which reverses
the order of the arguments and negates all of them:
`W_n(-x_n, …, -x₁) = W_n(x₁, …, x_n)` at Jost points. -/
