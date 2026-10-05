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

import Mathlib

/-!
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

open MeasureTheory Set

namespace Brockian.Weyl.DeficiencyODE

/-- `IsWeakSolution q z u v` says that the pair `(u, v)` is a *weak* solution of the
deficiency equation `u'' = (q - z) * u` of the Sturm–Liouville expression
`L u = -u'' + q u`, in the sense that `u` and `v` are merely continuous and satisfy the
integrated (Volterra) form of the system `u' = v`, `v' = (q - z) u`.

No differentiability whatsoever is assumed: this is the "weak regularity" hypothesis. -/
structure IsWeakSolution (q : ℝ → ℂ) (z : ℂ) (u v : ℝ → ℂ) : Prop where
  continuous_u : Continuous u
  continuous_v : Continuous v
  integral_u : ∀ t : ℝ, u t = u 0 + ∫ s in (0:ℝ)..t, v s
  integral_v : ∀ t : ℝ, v t = v 0 + ∫ s in (0:ℝ)..t, (q s - z) * u s

variable {q : ℝ → ℂ} {z : ℂ} {u v : ℝ → ℂ}

/-- A weak solution is automatically differentiable, with derivative the second component. -/

theorem exists_lipschitz_vectorField (hq : Continuous q) (z : ℂ) (T : ℝ) :
    ∃ K : NNReal, ∀ t ∈ Set.Ioo (-T) T,
      LipschitzOnWith K (fun y : ℂ × ℂ => (y.2, (q t - z) * y.1)) Set.univ := by
  rcases le_or_gt T (-T) with hT | hT
  · exact ⟨0, fun t ht => absurd (ht.1.trans ht.2) (by simpa using hT.not_gt)⟩
  have hne : (Set.Icc (-T) T).Nonempty := ⟨-T, le_refl _, le_of_lt hT⟩
  obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn hne
    (by fun_prop : ContinuousOn (fun s : ℝ => ‖q s - z‖) (Set.Icc (-T) T))
  refine ⟨⟨max 1 ‖q s₀ - z‖, le_trans zero_le_one (le_max_left _ _)⟩, ?_⟩
  intro t ht
  apply LipschitzOnWith.of_dist_le_mul
  intro x _ y _
  have hqt : ‖q t - z‖ ≤ max 1 ‖q s₀ - z‖ :=
    le_trans (hmax ⟨le_of_lt ht.1, le_of_lt ht.2⟩) (le_max_right _ _)
  rw [Prod.dist_eq, Prod.dist_eq]
  apply max_le
  · calc dist x.2 y.2 ≤ max (dist x.1 y.1) (dist x.2 y.2) := le_max_right _ _
      _ ≤ (max 1 ‖q s₀ - z‖) * max (dist x.1 y.1) (dist x.2 y.2) := by
          nlinarith [le_max_left (dist x.1 y.1) (dist x.2 y.2), dist_nonneg (x := x.1) (y := y.1),
            dist_nonneg (x := x.2) (y := y.2), le_max_left (1:ℝ) ‖q s₀ - z‖]
  · have heq : dist ((q t - z) * x.1) ((q t - z) * y.1) = ‖q t - z‖ * dist x.1 y.1 := by
      simp [dist_eq_norm, ← mul_sub]
    rw [heq]
    have h1 : dist x.1 y.1 ≤ max (dist x.1 y.1) (dist x.2 y.2) := le_max_left _ _
    have h2 := dist_nonneg (x := x.1) (y := y.1)
    calc ‖q t - z‖ * dist x.1 y.1 ≤ (max 1 ‖q s₀ - z‖) * dist x.1 y.1 :=
          mul_le_mul_of_nonneg_right hqt h2
      _ ≤ (max 1 ‖q s₀ - z‖) * max (dist x.1 y.1) (dist x.2 y.2) :=
          mul_le_mul_of_nonneg_left h1 (le_trans zero_le_one (le_max_left _ _))

/-- Uniqueness for the initial value problem in the weak formulation. -/
