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
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`counting S Λ` is the number of points of `S` that are `≤ Λ`. -/

theorem weylLawMatch_natSpec : WeylLawMatch natSpec 1 2 := by
  refine ⟨one_pos, two_pos, ?_⟩
  have key : Tendsto (fun Λ : ℝ => ((⌊Λ⌋₊ : ℝ) + 1) / Λ) atTop (𝓝 1) := by
    have hub : Tendsto (fun Λ : ℝ => 1 + 1 / Λ) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (X := ℝ) (α := ℝ) (x := (1 : ℝ)) (f := atTop)).add
        tendsto_inv_atTop_zero
      simpa [one_div] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
      rw [le_div_iff₀ hΛ, one_mul]
      linarith [Nat.lt_floor_add_one Λ]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
      rw [div_le_iff₀ hΛ]
      have : (⌊Λ⌋₊ : ℝ) ≤ Λ := Nat.floor_le hΛ.le
      field_simp
      nlinarith
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
  rw [counting_natSpec hΛ.le]
  norm_num [Real.rpow_one]

/-- The hypotheses of the main theorem are satisfiable, so the conclusion is not
vacuous: `natSpec` is discrete, matches a Weyl law, and its counting function
indeed diverges. -/
