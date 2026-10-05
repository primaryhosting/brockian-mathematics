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

theorem run_build (L : List (Fin n × Fin n)) (P : Equiv.Perm (Fin n) → Prop)
    (σ : Equiv.Perm (Fin n)) (hP : P σ) :
    P ((build L P).run σ) ∧
      ∀ p ∈ L, ((build L P).run σ p.1 < (build L P).run σ p.2 ↔ σ p.1 < σ p.2) := by
  induction L generalizing P with
  | nil =>
      have hex : ∃ τ, P τ := ⟨σ, hP⟩
      refine ⟨?_, by simp⟩
      simpa [build, run, hex] using hex.choose_spec
  | cons p rest ih =>
      obtain ⟨i, j⟩ := p
      by_cases hij : σ i < σ j
      · obtain ⟨h1, h2⟩ := ih (fun τ => P τ ∧ τ i < τ j) ⟨hP, hij⟩
        have hrun : (build ((i, j) :: rest) P).run σ
            = (build rest (fun τ => P τ ∧ τ i < τ j)).run σ := by simp [build, run, hij]
        rw [hrun]
        refine ⟨h1.1, ?_⟩
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact iff_of_true h1.2 hij
        · exact h2 q hq
      · obtain ⟨h1, h2⟩ := ih (fun τ => P τ ∧ ¬ τ i < τ j) ⟨hP, hij⟩
        have hrun : (build ((i, j) :: rest) P).run σ
            = (build rest (fun τ => P τ ∧ ¬ τ i < τ j)).run σ := by simp [build, run, hij]
        rw [hrun]
        refine ⟨h1.1, ?_⟩
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact iff_of_false h1.2 hij
        · exact h2 q hq

end CompTree

/-- Two arrangements of `Fin n` that give the same answer to every comparison
are equal. -/
