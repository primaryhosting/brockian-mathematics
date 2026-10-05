/-
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open MeasureTheory Metric Set

/-- The value of the Pfaffian (Euler) form of the Riemann curvature operator of a Riemannian
manifold of even dimension `2 * n` and constant sectional curvature `1`, measured against the
Riemannian volume form.

For constant sectional curvature `1` the curvature two-forms in an orthonormal coframe are
`Ω i j = e i ∧ e j`, and the classical Pfaffian
`Pf(Ω) = (2 ^ n * n !)⁻¹ * ∑ σ, sign σ • Ω (σ 1) (σ 2) ∧ ⋯ ∧ Ω (σ (2 * n - 1)) (σ (2 * n))`
evaluates to `(2 * n)! / (2 ^ n * n !)` times the volume form.  (For `n = 1` this is the
Gaussian curvature `K = 1` of the unit two-sphere.) -/

lemma volume_ball_odd (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (volume (ball (0 : EuclideanSpace ℝ (Fin (2 * n + 1))) r)).toReal =
      r ^ (2 * n + 1) * (Real.pi ^ n * 2 ^ (n + 1) / (2 * n + 1)‼) := by
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin]
  have hG : Real.Gamma ((2 * n + 1 : ℕ) / 2 + 1)
      = ((2 * (n + 1) - 1)‼ : ℕ) * Real.sqrt Real.pi / 2 ^ (n + 1) := by
    rw [← Real.Gamma_nat_add_half (n + 1)]
    congr 1
    push_cast
    ring
  have hpi : Real.sqrt Real.pi ^ (2 * n + 1) = Real.pi ^ n * Real.sqrt Real.pi := by
    rw [pow_succ, pow_mul, Real.sq_sqrt Real.pi_nonneg]
  have h2 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  have hs : Real.sqrt Real.pi > 0 := Real.sqrt_pos.2 Real.pi_pos
  have hd : ((2 * n + 1)‼ : ℝ) > 0 := by positivity
  rw [hG, hpi, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal]
  · rw [h2]
    field_simp
  · rw [h2]
    positivity

/-- Closed form for the Riemannian volume of the round `2 * n`-sphere of radius `r`:
`vol = (2 * n + 1) * 2 ^ (n + 1) * π ^ n / (2 * n + 1)‼ * r ^ (2 * n)`. -/
