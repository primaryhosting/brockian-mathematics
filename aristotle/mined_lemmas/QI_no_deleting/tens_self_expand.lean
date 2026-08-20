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

lemma tens_self_expand (p q : ℂ) :
    tens !₂[p, q] !₂[p, q]
      = (p * p) • tens ket0 ket0 + (p * q) • (tens ket0 ket1 + tens ket1 ket0)
        + (q * q) • tens ket1 ket1 := by
  ext r
  obtain ⟨i, j⟩ := r
  fin_cases i <;> fin_cases j <;> simp [tens, ket0, ket1, mul_comm]

/-- Expansion of `ψ ⊗ s` in the first factor, for `ψ = (p, q)`. -/
