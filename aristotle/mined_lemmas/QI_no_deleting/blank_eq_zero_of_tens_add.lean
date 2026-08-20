import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Setting

We work with a single qubit `H = EuclideanSpace ℂ (Fin 2)` and the two-qubit space
`K = EuclideanSpace ℂ (Fin 2 × Fin 2)`, with the tensor product of two one-qubit
states given explicitly by `QI.tens x y (i, j) = x i * y j`.

A *deleting machine* would be a unitary `U` on `K` together with a fixed "blank"
state `blank` such that `U (ψ ⊗ ψ) = ψ ⊗ blank` for every state `ψ`, i.e. one of
the two copies of the unknown state `ψ` is erased and replaced by the standard
blank state.  The no-deleting theorem says that no such unitary exists.
-/

namespace QI

/-- A single qubit. -/
abbrev H := EuclideanSpace ℂ (Fin 2)

/-- Two qubits. -/
abbrev K := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor product of two one-qubit states, in coordinates. -/

lemma blank_eq_zero_of_tens_add {blank : H}
    (h : tens ket0 blank + tens ket1 blank = 0) : blank = 0 := by
  ext j
  have hj : (tens ket0 blank + tens ket1 blank).ofLp (0, j) = (0 : K).ofLp (0, j) := by
    rw [h]
  simpa [tens, ket0, ket1] using hj

/-- **No deleting, linear version.**  Already the linearity of `U` (unitarity is not
needed) forbids a machine that maps `ψ ⊗ ψ` to `ψ ⊗ blank` for every unit vector `ψ`,
where `blank` is a fixed unit vector. -/
