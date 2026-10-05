import RequestProject.SimonQuantum

/-!
# Recovering the hidden shift from the measured samples

Each run of the quantum subroutine returns a uniformly random `y ∈ s^⊥`.  After `m`
runs the classical post-processing solves the linear system `t ⬝ y_i = 0` and outputs the
unique nonzero solution, which succeeds exactly when the samples *determine* `s`.
We bound the number of sample sequences that fail to determine `s`.
-/

open scoped BigOperators

namespace QI

variable {n : ℕ}

/-- The samples `y : Fin m → BV n` determine the hidden shift `s`: the only vectors
orthogonal to all of them are `0` and `s`. -/

theorem unique_solution_of_determines {s : BV n} (hs : s ≠ 0) {m : ℕ} {y : Fin m → BV n}
    (hmem : ∀ i, dotp s (y i) = 0) (hdet : Determines s y) :
    ∃! t : BV n, t ≠ 0 ∧ ∀ i, dotp t (y i) = 0 := by
  refine ⟨s, ⟨hs, hmem⟩, ?_⟩
  rintro t ⟨ht0, ht⟩
  rcases hdet t ht with h | h
  · exact absurd h ht0
  · exact h

/-- All sequences of `m` samples from the hyperplane `s^⊥`. -/
