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
