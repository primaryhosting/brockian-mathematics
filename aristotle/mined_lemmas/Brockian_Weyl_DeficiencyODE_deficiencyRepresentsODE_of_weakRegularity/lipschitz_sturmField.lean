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

open Set MeasureTheory

namespace Brockian.Weyl.DeficiencyODE

/-- **Weak regularity** of a potential `q : ℝ → ℂ`: `q` is bounded on every compact interval.
This is much weaker than continuity of `q`; it is exactly what is needed to run the Gronwall
argument behind uniqueness for the Sturm–Liouville system. -/

private theorem lipschitz_sturmField {R C : ℝ} (hC : ∀ t ∈ Set.Icc (-R) R, ‖q t‖ ≤ C)
    {t : ℝ} (ht : t ∈ Set.Icc (-R) R) :
    LipschitzOnWith (Real.toNNReal (max 1 (C + ‖z‖))) (sturmField q z t) Set.univ := by
  have hCnn : (0:ℝ) ≤ max 1 (C + ‖z‖) := le_trans zero_le_one (le_max_left _ _)
  have hqz : ‖q t - z‖ ≤ max 1 (C + ‖z‖) := by
    refine le_trans (le_trans (norm_sub_le _ _) ?_) (le_max_right _ _)
    have := hC t ht
    linarith
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x _ y _
  have hx : dist (sturmField q z t x) (sturmField q z t y)
      = max (dist x.2 y.2) (‖q t - z‖ * dist x.1 y.1) := by
    simp [sturmField, dist_eq_norm, ← mul_sub]
  rw [hx, Real.coe_toNNReal _ hCnn]
  have h1 : dist x.2 y.2 ≤ max 1 (C + ‖z‖) * dist x y := by
    calc dist x.2 y.2 ≤ dist x y := le_max_right _ _
      _ ≤ max 1 (C + ‖z‖) * dist x y := by
          nlinarith [dist_nonneg (x := x) (y := y), le_max_left 1 (C + ‖z‖)]
  have h2 : ‖q t - z‖ * dist x.1 y.1 ≤ max 1 (C + ‖z‖) * dist x y := by
    have hd : dist x.1 y.1 ≤ dist x y := le_max_left _ _
    have h0 : (0:ℝ) ≤ ‖q t - z‖ := norm_nonneg _
    nlinarith [dist_nonneg (x := x.1) (y := y.1), dist_nonneg (x := x) (y := y)]
  exact max_le h1 h2

/-- Uniqueness of solutions of the Sturm–Liouville system with vanishing Cauchy data:
a weakly regular potential forces a solution vanishing at `0` to vanish identically. -/
