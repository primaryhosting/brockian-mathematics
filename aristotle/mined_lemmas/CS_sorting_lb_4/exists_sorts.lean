import Mathlib

/-!
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- A comparison-based decision tree for sorting four elements.
Each internal node compares two positions `i j` of the input; the algorithm
branches on the answer.  Each leaf outputs a permutation (the claimed sorted
order of the input). -/
inductive CompTree : Type
  | leaf (out : Equiv.Perm (Fin 4)) : CompTree
  | node (i j : Fin 4) (l r : CompTree) : CompTree
  deriving Inhabited

namespace CompTree

/-- The worst-case number of comparisons performed by the tree. -/

theorem exists_sorts : ∃ t : CompTree, t.Sorts := by
  refine ⟨build Finset.univ allPairs, fun p => ?_⟩
  rw [run_build allPairs Finset.univ p (Finset.mem_univ p)]
  have : (Finset.univ.filter fun q : Equiv.Perm (Fin 4) =>
      ∀ ij ∈ allPairs, (q ij.1 < q ij.2 ↔ p ij.1 < p ij.2)) = {p} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨eq_of_allPairs p q, fun hq => by simp [hq]⟩
  rw [this]
  simp

end CompTree

/-- **Comparison-sort lower bound for 4 elements.**
Any comparison-based sorting algorithm on four elements, modelled as a decision
tree that correctly recovers the input ordering, performs at least
`⌈log₂ (4!)⌉ = 5` comparisons in the worst case. -/
