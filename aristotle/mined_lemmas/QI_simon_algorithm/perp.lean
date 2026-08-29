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

def perp (s : BV n) : Finset (BV n) := Finset.univ.filter (fun y => dotp s y = 0)

