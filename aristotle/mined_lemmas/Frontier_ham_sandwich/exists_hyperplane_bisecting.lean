/-
# Ham Sandwich
Category: Frontier Physics
Target: Frontier.ham_sandwich
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

open MeasureTheory Set Filter Topology

/-! ## A median for a finite measure on the real line -/

/-- Every finite Borel measure on `ℝ` admits a median: a point `c` such that both open
half-lines determined by `c` carry at most half of the total mass. -/

theorem exists_hyperplane_bisecting {n : ℕ} (hn : 0 < n) (μ : Measure (Fin n → ℝ))
    [IsFiniteMeasure μ] :
    ∃ (a : Fin n → ℝ) (c : ℝ), a ≠ 0 ∧
      μ (posHalf a c) ≤ μ univ / 2 ∧ μ (negHalf a c) ≤ μ univ / 2 := by
  obtain ⟨i0⟩ : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 hn
  have hfm : Measurable (fun x : Fin n → ℝ => x i0) := measurable_pi_apply i0
  set ν := Measure.map (fun x : Fin n → ℝ => x i0) μ with hν
  have hνuniv : ν univ = μ univ := by
    rw [hν, Measure.map_apply hfm MeasurableSet.univ]
    simp
  haveI : IsFiniteMeasure ν := ⟨by rw [hνuniv]; exact measure_lt_top μ _⟩
  obtain ⟨c, h1, h2⟩ := exists_median ν
  have hsum : ∀ x : Fin n → ℝ, (∑ i, (Pi.single i0 (1:ℝ) : Fin n → ℝ) i * x i) = x i0 := by
    intro x
    simp [Pi.single_apply, ite_mul, Finset.sum_ite_eq']
  refine ⟨Pi.single i0 1, c, ?_, ?_, ?_⟩
  · intro h
    have h' := congrFun h i0
    simp at h'
  · have hset : posHalf (Pi.single i0 (1:ℝ)) c = (fun x : Fin n → ℝ => x i0) ⁻¹' (Ioi c) := by
      ext x
      simp [posHalf, hsum x, mem_Ioi]
    rw [hset, ← Measure.map_apply hfm measurableSet_Ioi, ← hν, ← hνuniv]
    exact h2
  · have hset : negHalf (Pi.single i0 (1:ℝ)) c = (fun x : Fin n → ℝ => x i0) ⁻¹' (Iio c) := by
      ext x
      simp [negHalf, hsum x, mem_Iio]
    rw [hset, ← Measure.map_apply hfm measurableSet_Iio, ← hν, ← hνuniv]
    exact h1

/-- **Ham Sandwich theorem, base case `n = 1`.**
Any family of `n = 1` finite measures on `ℝ^n = ℝ^1` can be simultaneously bisected by a
single hyperplane `{x | ⟪a, x⟫ = c}` with `a ≠ 0`: each open half-space carries at most half
of the total mass of each measure. -/
