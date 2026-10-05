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

theorem shor_code_corrects (q r : Idx) (M N : Bool → Bool → ℂ) :
    ∃ c : ℂ, ∀ a b : Bool,
      ⟪qubitOp q M (codeword a), qubitOp r N (codeword b)⟫_ℂ = if a = b then c else 0 := by
  refine ⟨(8 : ℂ)⁻¹ * ∑ s : Bool × Bool × Bool,
      gmat q r M N (blockVal s q.1) (blockVal s r.1), ?_⟩
  intro a b
  rw [inner_codeword_errors]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    congr 1
    exact Finset.sum_congr rfl (fun s _ => by rw [sgn_mul_self, one_mul])
  · rw [if_neg hab]
    have h : ∀ s : Bool × Bool × Bool,
        sgn a s * sgn b s * gmat q r M N (blockVal s q.1) (blockVal s r.1) =
          sgn true s * gmat q r M N (blockVal s q.1) (blockVal s r.1) := by
      intro s; rw [sgn_mul_sgn_of_ne hab]
    rw [Finset.sum_congr rfl (fun s _ => h s), sum_sgn_true_mul, mul_zero]

/-! ## Nondegeneracy and error detection -/

/-- The identity `2 × 2` matrix, i.e. the trivial (no-)error on a qubit. -/
