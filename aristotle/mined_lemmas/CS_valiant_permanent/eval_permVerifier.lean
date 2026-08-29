import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

open Finset Matrix

/-! ## Part A: the 0/1 permanent as a counting problem -/

/-- For a 0/1 matrix, the permanent counts the permutations supported on the matrix, i.e. the
perfect matchings of the associated bipartite graph (equivalently, the cycle covers of the
associated digraph). -/

lemma eval_permVerifier (n : ℕ) (x y : Fin (n * n) → Bool) :
    (permVerifier n).eval (Sum.elim x y) = true ↔
      ((∀ i : Fin n, ∃! j : Fin n, y (finProdFinEquiv (i, j)) = true) ∧
       (∀ j : Fin n, ∃! i : Fin n, y (finProdFinEquiv (i, j)) = true) ∧
       (∀ i j : Fin n, y (finProdFinEquiv (i, j)) = true →
          x (finProdFinEquiv (i, j)) = true)) := by
  have hy : ∀ i j : Fin n, (yvar n i j).eval (Sum.elim x y) = y (finProdFinEquiv (i, j)) := by
    intro i j; rfl
  have hx : ∀ i j : Fin n, (xvar n i j).eval (Sum.elim x y) = x (finProdFinEquiv (i, j)) := by
    intro i j; rfl
  rw [permVerifier, Circuit.eval, Bool.and_eq_true, Circuit.eval, Bool.and_eq_true,
    Circuit.eval_bigAnd, Circuit.eval_bigAnd, Circuit.eval_bigAnd]
  refine and_congr ?_ (and_congr ?_ ?_)
  · constructor
    · intro h i
      have := h _ (List.mem_map_of_mem (List.mem_finRange i))
      rw [Circuit.eval_exactlyOne] at this
      simpa only [hy] using this
    · intro h c hc
      simp only [List.mem_map] at hc
      obtain ⟨i, -, rfl⟩ := hc
      rw [Circuit.eval_exactlyOne]
      simpa only [hy] using h i
  · constructor
    · intro h j
      have := h _ (List.mem_map_of_mem (List.mem_finRange j))
      rw [Circuit.eval_exactlyOne] at this
      simpa only [hy] using this
    · intro h c hc
      simp only [List.mem_map] at hc
      obtain ⟨j, -, rfl⟩ := hc
      rw [Circuit.eval_exactlyOne]
      simpa only [hy] using h j
  · constructor
    · intro h i j hij
      have hmem : Circuit.disj (Circuit.neg (yvar n i j)) (xvar n i j) ∈
          ((List.finRange n).flatMap fun i => (List.finRange n).map fun j =>
            Circuit.disj (Circuit.neg (yvar n i j)) (xvar n i j)) := by
        simp only [List.mem_flatMap, List.mem_map]
        exact ⟨i, List.mem_finRange i, j, List.mem_finRange j, rfl⟩
      have := h _ hmem
      simp only [Circuit.eval, hy, hx, hij, Bool.not_true, Bool.false_or] at this
      exact this
    · intro h c hc
      simp only [List.mem_flatMap, List.mem_map] at hc
      obtain ⟨i, -, j, -, rfl⟩ := hc
      simp only [Circuit.eval, hy, hx, Bool.or_eq_true, Bool.not_eq_true']
      by_cases hij : y (finProdFinEquiv (i, j)) = true
      · exact Or.inr (h i j hij)
      · exact Or.inl (by simpa using hij)

