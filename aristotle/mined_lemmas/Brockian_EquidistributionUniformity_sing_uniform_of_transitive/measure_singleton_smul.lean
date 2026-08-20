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
