/-
# Baire Category
Category: Pure Mathematics
Target: Math.baire_category
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Set

namespace Math

/-- **Baire category theorem.** A nonempty complete metric space is not the union of a
countable family of nowhere-dense sets: for any sequence `F : ℕ → Set X` of nowhere-dense
sets, `⋃ n, F n` is a proper subset of the space. -/
theorem baire_category {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (F : ℕ → Set X) (hF : ∀ n, IsNowhereDense (F n)) : (⋃ n, F n) ≠ univ := by
  intro hEq
  have hopen : ∀ n, IsOpen (closure (F n))ᶜ := fun n => isClosed_closure.isOpen_compl
  have hdense : ∀ n, Dense (closure (F n))ᶜ := fun n =>
    interior_eq_empty_iff_dense_compl.mp (hF n)
  obtain ⟨x, hx⟩ := (dense_iInter_of_isOpen hopen hdense).nonempty
  have hxU : x ∈ ⋃ n, F n := hEq ▸ mem_univ x
  obtain ⟨n, hn⟩ := mem_iUnion.1 hxU
  exact (mem_iInter.1 hx n) (subset_closure hn)

end Math

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

