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

theorem shor_codewords_orthonormal (a b : Bool) :
    ⟪codeword a, codeword b⟫_ℂ = if a = b then 1 else 0 := by
  rw [← qubitOp_idMat (0, 0) (codeword a), ← qubitOp_idMat (0, 0) (codeword b),
    inner_codeword_errors]
  have hg : ∀ u w : Bool, gmat ((0 : Fin 3), (0 : Fin 3)) (0, 0) idMat idMat u w = 1 := by
    intro u w
    rw [gmat_idMat_left]
    cases u <;> simp [idMat]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    have h : ∀ s : Bool × Bool × Bool,
        sgn a s * sgn a s * gmat ((0 : Fin 3), (0 : Fin 3)) (0, 0) idMat idMat
          (blockVal s (0 : Fin 3)) (blockVal s (0 : Fin 3)) = 1 := by
      intro s; rw [sgn_mul_self, one_mul, hg]
    rw [Finset.sum_congr rfl (fun s _ => h s)]
    simp
  · rw [if_neg hab]
    have h : ∀ s : Bool × Bool × Bool,
        sgn a s * sgn b s * gmat ((0 : Fin 3), (0 : Fin 3)) (0, 0) idMat idMat
            (blockVal s (0 : Fin 3)) (blockVal s (0 : Fin 3)) =
        sgn true s * gmat ((0 : Fin 3), (0 : Fin 3)) (0, 0) idMat idMat
            (blockVal s (0 : Fin 3)) (blockVal s (0 : Fin 3)) := by
      intro s; rw [sgn_mul_sgn_of_ne hab]
    rw [Finset.sum_congr rfl (fun s _ => h s), sum_sgn_true_mul, mul_zero]

/-- Every traceless single-qubit error (in particular every non-identity Pauli error) maps the
code space into its orthogonal complement: such errors are *detected*. -/
