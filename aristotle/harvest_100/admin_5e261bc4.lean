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
# Sing Uniform Of Transitive
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.sing_uniform_of_transitive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Brockian
namespace EquidistributionUniformity

open MeasureTheory

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
variable {G : Type*} [Group G] [MulAction G α]

/-- The mass of a singleton is invariant under the group action, for an invariant measure. -/
lemma measure_singleton_smul (μ : Measure α)
    (hinv : ∀ g : G, Measure.map (fun x : α => g • x) μ = μ) (g : G) (a : α) :
    μ {g • a} = μ {a} := by
  have hmeas : Measurable (fun x : α => g • x) := measurable_of_countable _
  have h := congrArg (fun ν : Measure α => ν {g • a}) (hinv g)
  simp only [Measure.map_apply hmeas (measurableSet_singleton _)] at h
  have hpre : (fun x : α => g • x) ⁻¹' {g • a} = {a} := by
    ext x
    simp [smul_left_cancel_iff]
  rw [hpre] at h
  exact h.symm

/-- Under a transitive action all singletons have the same mass. -/
lemma measure_singleton_eq_of_transitive (μ : Measure α)
    (hinv : ∀ g : G, Measure.map (fun x : α => g • x) μ = μ)
    (htrans : ∀ a b : α, ∃ g : G, g • a = b) (a b : α) :
    μ {a} = μ {b} := by
  obtain ⟨g, hg⟩ := htrans a b
  rw [← hg]
  exact (measure_singleton_smul μ hinv g a).symm

/-- **Equidistribution from transitivity.**  A probability measure on a finite space which is
invariant under a transitive group action assigns to every singleton the uniform mass
`1 / card α`. -/
theorem sing_uniform_of_transitive (μ : Measure α) [IsProbabilityMeasure μ]
    (hinv : ∀ g : G, Measure.map (fun x : α => g • x) μ = μ)
    (htrans : ∀ a b : α, ∃ g : G, g • a = b) (a : α) :
    μ {a} = 1 / (Fintype.card α : ENNReal) := by
  have hcard : (0 : ℕ) < Fintype.card α := Fintype.card_pos_iff.mpr ⟨a⟩
  have hsum : ∑ x : α, μ {x} = 1 := by
    rw [MeasureTheory.sum_measure_singleton]
    simp
  have hconst : ∀ x : α, μ {x} = μ {a} := fun x =>
    measure_singleton_eq_of_transitive μ hinv htrans x a
  have key : (Fintype.card α : ENNReal) * μ {a} = 1 := by
    calc (Fintype.card α : ENNReal) * μ {a}
        = ∑ _x : α, μ {a} := by
          simp [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = ∑ x : α, μ {x} := Finset.sum_congr rfl (fun x _ => (hconst x).symm)
      _ = 1 := hsum
  have hne : (Fintype.card α : ENNReal) ≠ 0 := by
    simpa using hcard.ne'
  have htop : (Fintype.card α : ENNReal) ≠ ⊤ := by simp
  exact (ENNReal.eq_div_iff hne htop).mpr key

end EquidistributionUniformity
end Brockian

