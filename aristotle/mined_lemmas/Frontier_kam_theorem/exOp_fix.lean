/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- The `n`-dimensional torus `𝕋ⁿ = (ℝ/ℤ)ⁿ`. -/
abbrev Torus (n : ℕ) : Type := Fin n → AddCircle (1 : ℝ)

/-- `W` parametrizes an invariant torus of the map `f` on which the dynamics is
conjugate to the rigid rotation by the frequency vector `ω`:
`f (W θ) = W (θ + ω)` for all angles `θ ∈ 𝕋ⁿ`. -/

private theorem exOp_fix (ω : Torus 1) (ε : ℝ) (W : C(Torus 1, ℝ)) :
    exOp ω ε W = W ↔ IsInvariantTorus (exFam ε) ω W := by
  constructor
  · intro h θ
    have := congrArg (fun (g : C(Torus 1, ℝ)) => g (θ + ω)) h
    simpa [exOp, exFam, add_sub_cancel_right, div_eq_mul_inv] using this
  · intro h
    ext θ
    have := h (θ - ω)
    simpa [exOp, exFam, sub_add_cancel, div_eq_mul_inv] using this

