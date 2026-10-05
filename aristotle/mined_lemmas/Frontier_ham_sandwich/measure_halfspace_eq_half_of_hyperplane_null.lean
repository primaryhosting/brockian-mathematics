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

theorem measure_halfspace_eq_half_of_hyperplane_null {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure μ]
    (v : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (h1 : μ Set.univ ≤ 2 * μ {x | inner ℝ v x ≤ c})
    (h2 : μ Set.univ ≤ 2 * μ {x | c ≤ inner ℝ v x})
    (h0 : μ {x | inner ℝ v x = c} = 0) :
    2 * μ {x | inner ℝ v x ≤ c} = μ Set.univ ∧
      2 * μ {x | c ≤ inner ℝ v x} = μ Set.univ := by
  set f : EuclideanSpace ℝ (Fin n) → ℝ := fun x => inner ℝ v x with hf
  have hfm : Measurable f := ((innerSL ℝ v).continuous).measurable
  set A : Set (EuclideanSpace ℝ (Fin n)) := {x | f x ≤ c} with hA
  set B : Set (EuclideanSpace ℝ (Fin n)) := {x | c ≤ f x} with hB
  have hAm : MeasurableSet A := hfm measurableSet_Iic
  have hBm : MeasurableSet B := hfm measurableSet_Ici
  have hunion : A ∪ B = Set.univ := by
    ext x
    simp only [hA, hB, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact le_total (f x) c
  have hinter : A ∩ B = {x | f x = c} := by
    ext x
    simp only [hA, hB, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩
  have hsum : μ A + μ B = μ Set.univ := by
    have := measure_union_add_inter (μ := μ) A hBm
    rw [hunion, hinter, h0, add_zero] at this
    exact this.symm
  have hAfin : μ A ≠ ⊤ := measure_ne_top _ _
  have hBfin : μ B ≠ ⊤ := measure_ne_top _ _
  have hBA : μ B ≤ μ A := by
    rw [← hsum, two_mul] at h1
    exact (ENNReal.add_le_add_iff_left hAfin).1 h1
  have hAB : μ A ≤ μ B := by
    rw [← hsum] at h2
    have : μ B + μ A ≤ μ B + μ B := by rw [add_comm (μ B) (μ A)]; rw [two_mul] at h2; exact h2
    exact (ENNReal.add_le_add_iff_left hBfin).1 this
  have hEq : μ A = μ B := le_antisymm hAB hBA
  constructor
  · rw [two_mul, ← hsum, hEq]
  · rw [two_mul, ← hsum, hEq]

end Frontier

