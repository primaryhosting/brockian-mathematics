/-
# Ham Sandwich
Category: Frontier Physics
Target: Frontier.ham_sandwich
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ham Sandwich
Category: Frontier Physics
Target: Frontier.ham_sandwich
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory Filter Set Topology
open scoped ENNReal

/-!
## Step 1: existence of a median for a finite measure on `ℝ`

A *median* of a finite measure `ν` on `ℝ` is a point `c` such that both closed half-lines
`Iic c` and `Ici c` carry at least half of the total mass.  This is the one-dimensional
form of "bisection by a hyperplane"; it is obtained by taking `c` to be the infimum of the
set of points where the cumulative distribution function has reached half of the total mass.
-/

/-- **Existence of a median.**  Every finite measure `ν` on `ℝ` admits a point `c` such that
each of the two closed half-lines determined by `c` carries at least half of the total mass. -/

theorem exists_bisecting_hyperplane {n : ℕ} (hn : 0 < n)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure μ] :
    ∃ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ), v ≠ 0 ∧
      μ Set.univ ≤ 2 * μ {x | inner ℝ v x ≤ c} ∧
      μ Set.univ ≤ 2 * μ {x | c ≤ inner ℝ v x} := by
  set v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ) with hv
  have hv0 : v ≠ 0 := by simp [hv, EuclideanSpace.single_eq_zero_iff]
  set f : EuclideanSpace ℝ (Fin n) → ℝ := fun x => inner ℝ v x with hf
  have hfc : Continuous f := (innerSL ℝ v).continuous
  have hfm : Measurable f := hfc.measurable
  obtain ⟨c, h1, h2⟩ := exists_median (μ.map f)
  refine ⟨v, c, hv0, ?_, ?_⟩
  · rwa [Measure.map_apply hfm MeasurableSet.univ,
      Measure.map_apply hfm measurableSet_Iic, Set.preimage_univ] at h1
  · rwa [Measure.map_apply hfm MeasurableSet.univ,
      Measure.map_apply hfm measurableSet_Ici, Set.preimage_univ] at h2

/-!
## Step 3: the Ham–Sandwich statement
-/

/-- The Ham–Sandwich property in dimension `n`: any `n` finite measures on `ℝⁿ` can be
simultaneously bisected by a single affine hyperplane `{x | ⟪v, x⟫ = c}` with `v ≠ 0`,
in the sense that for each of the measures both closed half-spaces bounded by the
hyperplane carry at least half of the total mass. -/
