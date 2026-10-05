import Mathlib
/-!
# Baire Category
Category: Pure Mathematics
Target: Math.baire_category
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Set Topology

variable {X : Type*} [MetricSpace X] [CompleteSpace X]

/-- The complement of the closure of a nowhere dense set is open and dense. -/
lemma isOpen_dense_compl_closure_of_isNowhereDense {s : Set X} (hs : IsNowhereDense s) :
    IsOpen (closure s)ᶜ ∧ Dense (closure s)ᶜ := by
  refine ⟨isClosed_closure.isOpen_compl, ?_⟩
  exact interior_eq_empty_iff_dense_compl.mp hs

/-- **Baire category theorem**: a nonempty complete metric space is not the union of a countable
family of nowhere dense sets. -/
theorem baire_category [Nonempty X] (s : ℕ → Set X) (hs : ∀ n, IsNowhereDense (s n)) :
    (⋃ n, s n) ≠ (univ : Set X) := by
  intro hcov
  have hdense : Dense (⋂ n, (closure (s n))ᶜ) :=
    dense_iInter_of_isOpen_nat
      (fun n => (isOpen_dense_compl_closure_of_isNowhereDense (hs n)).1)
      (fun n => (isOpen_dense_compl_closure_of_isNowhereDense (hs n)).2)
  obtain ⟨x, hx⟩ := hdense.nonempty
  obtain ⟨n, hn⟩ := mem_iUnion.1 (hcov ▸ mem_univ x : x ∈ ⋃ n, s n)
  exact (mem_iInter.1 hx n) (subset_closure hn)

end Math

