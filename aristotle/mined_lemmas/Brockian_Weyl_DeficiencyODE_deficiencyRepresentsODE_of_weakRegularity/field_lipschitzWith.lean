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

open Set MeasureTheory

namespace Brockian.Weyl.DeficiencyODE

/-- **Weak regularity of the potential.** The coefficient `q` is bounded on every compact
interval.  This is far weaker than continuity (no measurability, no smoothness); it is exactly
the amount of regularity needed for Weyl's deficiency theory of the Sturm–Liouville expression
`τ u = -u'' + q u`. -/

lemma field_lipschitzWith (t : ℝ) {K : NNReal} (h1 : (1 : ℝ) ≤ (K : ℝ))
    (h2 : ‖q t - z‖ ≤ (K : ℝ)) : LipschitzWith K (field q z t) := by
  apply LipschitzWith.of_dist_le_mul
  intro Y W
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have hm1 : dist Y.1 W.1 ≤ max (dist Y.1 W.1) (dist Y.2 W.2) := le_max_left _ _
  have hm2 : dist Y.2 W.2 ≤ max (dist Y.1 W.1) (dist Y.2 W.2) := le_max_right _ _
  have hmnn : (0 : ℝ) ≤ max (dist Y.1 W.1) (dist Y.2 W.2) := le_trans dist_nonneg hm1
  have hmul : dist ((q t - z) * Y.1) ((q t - z) * W.1) = ‖q t - z‖ * dist Y.1 W.1 := by
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul]
  rw [Prod.dist_eq, Prod.dist_eq]
  simp only [field]
  refine max_le ?_ ?_
  · calc dist Y.2 W.2 ≤ max (dist Y.1 W.1) (dist Y.2 W.2) := hm2
      _ ≤ (K : ℝ) * max (dist Y.1 W.1) (dist Y.2 W.2) := le_mul_of_one_le_left hmnn h1
  · rw [hmul]
    exact mul_le_mul h2 hm1 dist_nonneg hK0

/-- **Uniqueness for the Sturm–Liouville initial value problem** under weak regularity only:
two global phase-space solutions with the same value at one point coincide. -/
