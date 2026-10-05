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

private theorem exOp_lipschitz (ω : Torus 1) (ε : ℝ) :
    LipschitzWith ⟨1/2, by norm_num⟩ (exOp ω ε) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro W W'
  refine (ContinuousMap.dist_le (by positivity)).2 ?_
  intro θ
  have h : dist (W (θ - ω)) (W' (θ - ω)) ≤ dist W W' :=
    ContinuousMap.dist_apply_le_dist _
  simp only [exOp, ContinuousMap.coe_mk, Real.dist_eq]
  have : (W (θ - ω) / 2 + ε) - (W' (θ - ω) / 2 + ε) = (W (θ - ω) - W' (θ - ω)) / 2 := by ring
  rw [this, abs_div]
  rw [Real.dist_eq] at h
  simp only [NNReal.coe_mk]
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  linarith

/-- The hypotheses of `kam_theorem` are satisfiable: for the explicit family
`f ε x = x / 2 + ε` on `ℝ` and any frequency `ω`, the invariant torus of the unperturbed
system persists under the `ε`-perturbation and stays `2 * ε`-close to it. -/
