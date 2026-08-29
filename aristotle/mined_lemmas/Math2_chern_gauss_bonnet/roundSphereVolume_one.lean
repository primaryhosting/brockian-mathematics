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

lemma roundSphereVolume_one (n : ℕ) :
    roundSphereVolume n 1 =
      (Measure.toSphere (volume : Measure (EuclideanSpace ℝ (Fin (2 * n + 1))))).real univ := by
  rw [Measure.toSphere_real_apply_univ, finrank_euclidean, roundSphereVolume]
  simp [measureReal_def]

/-- Closed form for the volume of a ball of radius `r` in odd-dimensional Euclidean space. -/
