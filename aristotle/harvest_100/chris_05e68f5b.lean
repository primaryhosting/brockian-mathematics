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
# Equidistribution from transitivity

If a group `G` acts transitively on a finite type `α` and `μ` is a `G`-invariant probability
measure on `α`, then `μ` is the uniform distribution: every singleton has measure
`(Fintype.card α)⁻¹`.

The main result is `Brockian.EquidistributionUniformity.sing_uniform_of_transitive`, stated
unconditionally (no auxiliary named hypothesis beyond invariance of the measure).
-/

open MeasureTheory

namespace Brockian
namespace EquidistributionUniformity

variable {G α : Type*}

/-- On a finite type whose singletons are measurable, every set is measurable. -/
theorem measurableSet_of_finite [Finite α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (s : Set α) : MeasurableSet s :=
  (Set.toFinite s).measurableSet

/-- On a finite type whose singletons are measurable, every function out of it is measurable. -/
theorem measurable_of_finite {β : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace β] (f : α → β) : Measurable f :=
  fun s _ => measurableSet_of_finite (f ⁻¹' s)

/-- A `G`-invariant measure gives the same mass to `{x}` and `{g • x}`. -/
theorem measure_singleton_smul [Group G] [MulAction G α] [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ : Measure α}
    (hinv : ∀ g : G, Measure.map (fun x : α => g • x) μ = μ) (g : G) (x : α) :
    μ {g • x} = μ {x} := by
  have hmap := hinv g
  have h : Measure.map (fun x : α => g • x) μ {g • x} = μ {g • x} := by rw [hmap]
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_of_finite _)] at h
  have hpre : (fun x : α => g • x) ⁻¹' {g • x} = {x} := by
    ext y
    simp [Set.mem_preimage, smul_left_cancel_iff]
  rw [hpre] at h
  exact h.symm

/-- If the action is transitive, an invariant measure gives all singletons the same mass. -/
theorem measure_singleton_eq_of_transitive [Group G] [MulAction G α]
    [MulAction.IsPretransitive G α] [Finite α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ : Measure α} (hinv : ∀ g : G, Measure.map (fun x : α => g • x) μ = μ) (x y : α) :
    μ {x} = μ {y} := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
  rw [← hg]
  exact (measure_singleton_smul hinv g x).symm

/-- The total mass of a measure on a finite type is the sum of the masses of the singletons. -/
theorem measure_univ_eq_sum [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) : μ Set.univ = ∑ x : α, μ {x} := by
  simp

/-- **Equidistribution from transitivity.**  If a group `G` acts transitively on a finite
type `α`, then any `G`-invariant probability measure on `α` is uniform: every
singleton has measure `(Fintype.card α)⁻¹`. -/
theorem sing_uniform_of_transitive [Group G] [MulAction G α] [MulAction.IsPretransitive G α]
    [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (hinv : ∀ g : G, Measure.map (fun x : α => g • x) μ = μ) (x : α) :
    μ {x} = (Fintype.card α : ENNReal)⁻¹ := by
  have hsum : (1 : ENNReal) = (Fintype.card α : ENNReal) * μ {x} := by
    have h := measure_univ_eq_sum μ
    rw [measure_univ] at h
    calc (1 : ENNReal) = ∑ _y : α, μ {x} := by
          rw [h]
          exact Finset.sum_congr rfl fun y _ => measure_singleton_eq_of_transitive hinv y x
      _ = (Fintype.card α : ENNReal) * μ {x} := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hsum.symm)

/-!
### Non-vacuity

The hypotheses of `sing_uniform_of_transitive` are satisfiable: a finite group acting on
itself by left translation is transitive, and the normalized counting measure is invariant.
-/

/-- The counting measure on a finite type is invariant under any bijection. -/
theorem map_count_equiv [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (e : α ≃ α) : Measure.map e (Measure.count) = (Measure.count : Measure α) := by
  ext s hs
  rw [Measure.map_apply (measurable_of_finite _) hs,
    Measure.count_apply_finite _ (Set.toFinite _), Measure.count_apply_finite _ (Set.toFinite _)]
  congr 1
  rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _),
    ← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  exact Set.ncard_preimage_of_injective_subset_range e.injective
    (by simp [e.surjective.range_eq])

/-- The uniform (normalized counting) measure on a finite type. -/
noncomputable def uniformMeasure (α : Type*) [Fintype α] [MeasurableSpace α] : Measure α :=
  (Fintype.card α : ENNReal)⁻¹ • Measure.count

instance [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] :
    IsProbabilityMeasure (uniformMeasure α) := by
  constructor
  rw [uniformMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.count_apply_finite _ (Set.toFinite _)]
  simp only [Set.Finite.toFinset_univ, Finset.card_univ]
  rw [ENNReal.inv_mul_cancel (by simp [Fintype.card_ne_zero]) (by simp)]

/-- The uniform measure on a finite group is invariant under left translation. -/
theorem map_uniformMeasure_mul_left [Group G] [Fintype G] [MeasurableSpace G]
    [MeasurableSingletonClass G] (g : G) :
    Measure.map (fun x : G => g • x) (uniformMeasure G) = uniformMeasure G := by
  rw [uniformMeasure, Measure.map_smul]
  congr 1
  exact map_count_equiv (Equiv.mulLeft g)

/-- Instance of the main theorem: on a finite group, the uniform measure assigns mass
`(Fintype.card G)⁻¹` to each singleton. -/
example [Group G] [Fintype G] [MeasurableSpace G] [MeasurableSingletonClass G] (x : G) :
    uniformMeasure G {x} = (Fintype.card G : ENNReal)⁻¹ :=
  sing_uniform_of_transitive (G := G) (uniformMeasure G) map_uniformMeasure_mul_left x

end EquidistributionUniformity
end Brockian

