import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ComplexConjugate
open scoped InnerProductSpace

namespace QI

/-! ## Setup

Nine qubits, indexed by `Idx = Fin 3 × Fin 3`: the first component is the block
(one of the three "outer" repetition-code slots), the second is the position of the
qubit inside its block.  A computational basis state is a bit string `Idx → Bool`,
and the state space is the corresponding `512`-dimensional complex Hilbert space. -/

/-- Index of a qubit: `(block, position within block)`. -/
abbrev Idx := Fin 3 × Fin 3

/-- Computational basis states of the nine qubits. -/
abbrev BasisIdx := Idx → Bool

/-- The nine-qubit state space. -/
abbrev QState := EuclideanSpace ℂ BasisIdx

/-- The operator acting as the `2 × 2` matrix `M` on qubit `q` and as the identity
on the remaining eight qubits.  Every single-qubit error on qubit `q` is of this form. -/

theorem shor_code_detects_traceless (q : Idx) (P : Bool → Bool → ℂ)
    (hP : P false false + P true true = 0) (a b : Bool) :
    ⟪codeword a, qubitOp q P (codeword b)⟫_ℂ = 0 := by
  rw [← qubitOp_idMat q (codeword a), inner_codeword_errors]
  simp only [gmat_idMat_left]
  by_cases hab : a = b
  · subst hab
    have h : ∀ s : Bool × Bool × Bool,
        sgn a s * sgn a s * P (blockVal s q.1) (blockVal s q.1) =
          P (blockVal s q.1) (blockVal s q.1) := by
      intro s; rw [sgn_mul_self, one_mul]
    rw [Finset.sum_congr rfl (fun s _ => h s), sum_blockVal q.1 P, hP, mul_zero, mul_zero]
  · have h : ∀ s : Bool × Bool × Bool,
        sgn a s * sgn b s * P (blockVal s q.1) (blockVal s q.1) =
          sgn true s * P (blockVal s q.1) (blockVal s q.1) := by
      intro s; rw [sgn_mul_sgn_of_ne hab]
    rw [Finset.sum_congr rfl (fun s _ => h s), sum_sgn_true_mul, mul_zero]

/-- The Pauli `X` matrix. -/
