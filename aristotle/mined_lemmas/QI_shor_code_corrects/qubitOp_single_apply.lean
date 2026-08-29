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

lemma qubitOp_single_apply (q : Idx) (M : Bool → Bool → ℂ) (y x : BasisIdx) :
    (qubitOp q M) (EuclideanSpace.single y (1 : ℂ)) x =
      if Function.update x q (y q) = y then M (x q) (y q) else 0 := by
  show ∑ b : Bool, M (x q) b * (EuclideanSpace.single y (1:ℂ)) (Function.update x q b) = _
  rw [Finset.sum_eq_single (y q)]
  · simp [EuclideanSpace.single_apply]
  · intro b _ hb
    simp only [EuclideanSpace.single_apply, mul_ite, mul_one, mul_zero, ite_eq_right_iff]
    intro h
    exact absurd (by rw [← h]; simp) hb
  · simp

