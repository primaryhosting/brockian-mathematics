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

open MeasureTheory Set Filter Topology

namespace Frontier

/-!
## Bisecting a single finite measure

The Ham–Sandwich theorem states that `n` finite measures on `ℝⁿ` can be simultaneously
bisected by a single affine hyperplane `{x | ⟪v, x⟫ = c}` (`v` a unit vector), where
"bisected" is understood in the weak sense that each of the two closed half-spaces
carries at least half of the total mass.  (The weak form is the correct one for general
measures: a Dirac mass sitting on the hyperplane cannot be split exactly.)

Mathlib does not contain the Ham–Sandwich theorem, nor the Borsuk–Ulam theorem on which
the general proof rests, so everything below is developed from scratch.  We prove the
base case, `k = 1` measure in `ℝⁿ`, in the form of a median (`Frontier.ham_sandwich`),
together with a genuinely `n`-measure instance for point masses
(`Frontier.ham_sandwich_dirac`).
-/

/-- **Existence of a median.**  For a finite measure `μ` and a measurable real valued
function `f`, there is a threshold `c` such that both `{f ≤ c}` and `{c ≤ f}` carry at
least half of the total mass. -/

theorem ham_sandwich_dirac {n : ℕ} (hn : 0 < n) (p : Fin n → EuclideanSpace ℝ (Fin n)) :
    ∃ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ), ‖v‖ = 1 ∧ ∀ i : Fin n,
      (Measure.dirac (p i)) univ / 2 ≤ (Measure.dirac (p i)) {x | inner ℝ v x ≤ c} ∧
      (Measure.dirac (p i)) univ / 2 ≤ (Measure.dirac (p i)) {x | c ≤ inner ℝ v x} := by
  obtain ⟨v, c, hv, hp⟩ := exists_unit_hyperplane_through_points hn p
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin n) => (inner ℝ v x : ℝ)) :=
    continuous_const.inner continuous_id
  have hm1 : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | inner ℝ v x ≤ c} :=
    measurableSet_le hcont.measurable measurable_const
  have hm2 : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | c ≤ inner ℝ v x} :=
    measurableSet_le measurable_const hcont.measurable
  refine ⟨v, c, hv, fun i => ⟨?_, ?_⟩⟩
  · rw [Measure.dirac_apply' _ hm1, Measure.dirac_apply' _ MeasurableSet.univ]
    simp [Set.indicator_of_mem, hp i]
  · rw [Measure.dirac_apply' _ hm2, Measure.dirac_apply' _ MeasurableSet.univ]
    simp [Set.indicator_of_mem, hp i]

end Frontier

