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

noncomputable def qubitOp (q : Idx) (M : Bool → Bool → ℂ) : QState →ₗ[ℂ] QState where
  toFun f := (WithLp.toLp 2 (fun x => ∑ b : Bool, M (x q) b * f (Function.update x q b)))
  map_add' f g := by ext x; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by ext x; simp; ring

/-- The value carried by block `i` in a triple of block values. -/
