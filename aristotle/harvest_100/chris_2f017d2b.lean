/-
# Baire Category
Category: Pure Mathematics
Target: Math.baire_category
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Baire Category
Category: Pure Mathematics
Target: Math.baire_category
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Set

namespace Math

/-- **Baire category theorem.** A nonempty complete metric space is not the union of a
countable family of nowhere dense subsets.

Proof: the complement of the closure of each nowhere dense set is open and dense, so by the
Baire property of complete metric spaces (`dense_iInter_of_isOpen`, whose `BaireSpace`
instance for complete pseudometric spaces is
`BaireSpace.of_pseudoEMetricSpace_completeSpace` in Mathlib) the intersection of these
complements is dense, hence nonempty; any of its points lies outside the union. -/
theorem baire_category {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {ι : Type*} [Countable ι] (s : ι → Set X) (hs : ∀ i, IsNowhereDense (s i)) :
    (⋃ i, s i) ≠ univ := by
  intro h
  have hopen : ∀ i, IsOpen (closure (s i))ᶜ := fun i => isClosed_closure.isOpen_compl
  have hdense : ∀ i, Dense (closure (s i))ᶜ := by
    intro i
    rw [← interior_eq_empty_iff_dense_compl]
    exact hs i
  obtain ⟨x, hx⟩ := (dense_iInter_of_isOpen hopen hdense).nonempty
  simp only [mem_iInter, mem_compl_iff] at hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (h ▸ mem_univ x)
  exact hx i (subset_closure hi)

/-- Sequence form: a nonempty complete metric space is not a countable union `⋃ n, s n`
of nowhere dense sets. -/
theorem baire_category_seq {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (s : ℕ → Set X) (hs : ∀ n, IsNowhereDense (s n)) : (⋃ n, s n) ≠ univ :=
  baire_category s hs

end Math

#print axioms Math.baire_category

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

