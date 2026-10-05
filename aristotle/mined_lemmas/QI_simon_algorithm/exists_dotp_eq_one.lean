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

lemma exists_dotp_eq_one {s : BV n} (hs : s ≠ 0) : ∃ a : BV n, dotp s a = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hs (funext fun i => h i)
  refine ⟨e i, ?_⟩
  rcases QI.ZMod.two_cases (s i) with h0 | h1
  · exact absurd h0 hi
  · simpa using h1

/-- The hyperplane `s^⊥` has `2^(n-1)` elements: `2 * |s^⊥| = 2^n`. -/
