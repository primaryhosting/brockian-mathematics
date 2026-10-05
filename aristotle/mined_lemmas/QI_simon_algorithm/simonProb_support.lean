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

theorem simonProb_support {β : Type*} [DecidableEq β] {s : BV n} {f : BV n → β}
    (hf : IsSimon s f) {y : BV n} (hy : simonProb f y ≠ 0) : dotp s y = 0 := by
  by_contra h
  rw [simonProb_eq hf y, if_neg h] at hy
  exact hy rfl

end QI

