/-
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-- A comparison-based sorting algorithm for `n` elements, modelled as a binary
decision tree.  An internal node `node i j l r` compares the inputs at positions
`i` and `j`, descending into `l` if `a i < a j` and into `r` otherwise; a leaf
`leaf p` outputs the permutation `p`. -/
inductive CompTree (n : ℕ) : Type
  | leaf : Equiv.Perm (Fin n) → CompTree n
  | node : Fin n → Fin n → CompTree n → CompTree n → CompTree n
  deriving Inhabited

namespace CompTree

variable {n : ℕ}

/-- The worst-case number of comparisons performed by the algorithm, i.e. the
height of the decision tree. -/

theorem exists_correct_tree (n : ℕ) :
    ∃ t : CompTree n, ∀ σ : Equiv.Perm (Fin n), t.run σ = σ := by
  classical
  refine ⟨CompTree.build (Finset.univ : Finset (Fin n × Fin n)).toList (fun _ => True), ?_⟩
  intro σ
  obtain ⟨-, h2⟩ :=
    CompTree.run_build (Finset.univ : Finset (Fin n × Fin n)).toList (fun _ => True) σ trivial
  exact perm_eq_of_lt_iff σ _ fun i j => h2 (i, j) (by simp)

/-- **Comparison-sorting lower bound for 4 elements.**
Any correct comparison sort of 4 elements — modelled as a binary decision tree
whose internal nodes compare two input positions and whose leaves output the
sorting permutation — performs at least `⌈log₂ (4!)⌉ = 5` comparisons in the
worst case. -/
