/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Metric Filter Topology

/-- A parameterization `K : Θ → P` of a torus is *invariant* for the dynamics `F : P → P`
with internal (rigid rotation) dynamics `R : Θ → Θ` if it conjugates `R` to `F`:
`F (K θ) = K (R θ)` for all `θ`.  This is the standard "parameterization method"
formulation of an invariant torus carrying quasi-periodic motion with rotation `R`. -/

theorem kam_invariant_circle_of_skew_product
    (α : AddCircle (1 : ℝ)) (lam : ℝ) (hlam : |lam| < 1)
    (g : C(AddCircle (1 : ℝ), ℝ)) (ε : ℝ) :
    ∃ u : C(AddCircle (1 : ℝ), ℝ),
      IsInvariantTorus (fun q : AddCircle (1 : ℝ) × ℝ => (q.1 + α, lam * q.2 + ε * g q.1))
        (fun x => x + α) (fun x => (x, u x)) ∧
      ‖u‖ ≤ |ε| * ‖g‖ / (1 - |lam|) := by
  classical
  -- the invariance operator: `u` parameterizes an invariant circle iff it is a fixed point
  set T : ℝ → C(AddCircle (1:ℝ), ℝ) → C(AddCircle (1:ℝ), ℝ) := fun δ u =>
    ⟨fun x => lam * u (x - α) + δ * g (x - α), by fun_prop⟩ with hT
  have hlip : ∀ δ : ℝ, LipschitzWith ‖lam‖₊ (T δ) := by
    intro δ
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    refine (ContinuousMap.dist_le (by positivity)).2 fun x => ?_
    have hx : dist (u (x - α)) (v (x - α)) ≤ dist u v := ContinuousMap.dist_apply_le_dist _
    have : dist ((T δ u) x) ((T δ v) x) = |lam| * dist (u (x - α)) (v (x - α)) := by
      simp [hT, Real.dist_eq, ← mul_sub, abs_mul]
    rw [this]
    have : (‖lam‖₊ : ℝ) = |lam| := by simp [Real.norm_eq_abs]
    rw [this]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg lam)
  have hzero : T 0 0 = 0 := by
    ext x; simp [hT]
  have hc : ∀ δ : ℝ, dist (T δ 0) 0 ≤ ‖g‖ * |δ| := by
    intro δ
    refine (ContinuousMap.dist_le (by positivity)).2 fun x => ?_
    have : dist ((T δ 0) x) ((0 : C(AddCircle (1:ℝ), ℝ)) x) = |δ| * |g (x - α)| := by
      simp [hT]
    rw [this, mul_comm (‖g‖) |δ|]
    have : |g (x - α)| ≤ ‖g‖ := by
      simpa [Real.norm_eq_abs] using g.norm_coe_le_norm (x - α)
    exact mul_le_mul_of_nonneg_left this (abs_nonneg δ)
  have hsol : ∀ (δ : ℝ) (u : C(AddCircle (1:ℝ), ℝ)), T δ u = u →
      IsInvariantTorus (fun q : AddCircle (1 : ℝ) × ℝ => (q.1 + α, lam * q.2 + δ * g q.1))
        (fun x => x + α) (fun x => (x, u x)) := by
    intro δ u hu x
    have hux : (T δ u) (x + α) = u (x + α) := by rw [hu]
    simp only [hT, ContinuousMap.coe_mk, add_sub_cancel_right] at hux
    simp [hux]
  have hL : ‖lam‖₊ < 1 := by
    have : (‖lam‖₊ : ℝ) = |lam| := by simp [Real.norm_eq_abs]
    rw [← NNReal.coe_lt_coe, this]
    simpa using hlam
  obtain ⟨u, hinv, -, hdist, -, -⟩ :=
    kam_theorem (fun δ => fun q : AddCircle (1 : ℝ) × ℝ => (q.1 + α, lam * q.2 + δ * g q.1))
      (fun x : AddCircle (1:ℝ) => x + α) (fun u : C(AddCircle (1:ℝ), ℝ) => fun x => (x, u x)) T
      hsol ‖lam‖₊ hL hlip 0 hzero ‖g‖ hc ε
  refine ⟨u, hinv, ?_⟩
  have hnorm : ‖u‖ = dist u 0 := by simp [dist_eq_norm]
  have hcoe : ((‖lam‖₊ : ℝ)) = |lam| := by simp [Real.norm_eq_abs]
  rw [hnorm]
  calc dist u 0 ≤ ‖g‖ * |ε| / (1 - (‖lam‖₊ : ℝ)) := hdist
    _ = |ε| * ‖g‖ / (1 - |lam|) := by rw [hcoe, mul_comm]

end Frontier

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

