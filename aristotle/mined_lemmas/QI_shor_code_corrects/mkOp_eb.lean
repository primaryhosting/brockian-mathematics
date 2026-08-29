import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ComplexConjugate

namespace QI

/-! ## The 9-qubit Hilbert space -/

/-- Labels for the computational basis of 9 qubits. -/
abbrev Q := Fin 9 → Bool

/-- The state space of 9 qubits, `ℂ^(2^9)` with its standard Hermitian inner product. -/
abbrev H := EuclideanSpace ℂ Q

/-- Flip the `i`-th bit of a basis label. -/

lemma mkOp_eb (co : Q → ℂ) (g : Q → Q) (hg : ∀ b, g (g b) = b) (c : Q) :
    mkOp co g (eb c) = co (g c) • eb (g c) := by
  ext b
  rw [eb, mkOp_apply]
  simp only [eb, EuclideanSpace.single_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases h : b = g c
  · subst h; rw [hg]; simp
  · have : g b ≠ c := by intro hh; exact h (by rw [← hh, hg])
    simp [this, h]

/-! ## Single-qubit Pauli operators -/

/-- Names of the four single-qubit Pauli matrices. -/
inductive P1 | I | X | Y | Z
  deriving DecidableEq

open P1

/-- Basis-label permutation implemented by a Pauli. -/
