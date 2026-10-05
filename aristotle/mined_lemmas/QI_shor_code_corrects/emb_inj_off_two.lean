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

lemma emb_inj_off_two {s t : Bool × Bool × Bool} {q r : Idx}
    (h : ∀ p : Idx, p ≠ q → p ≠ r → emb s p = emb t p) : s = t := by
  have key : ∀ (q r : Idx) (i : Fin 3), ∃ j : Fin 3, ((i, j) ≠ q ∧ (i, j) ≠ r) := by decide
  have hb : ∀ i, blockVal s i = blockVal t i := by
    intro i
    obtain ⟨j, hj1, hj2⟩ := key q r i
    have := h (i, j) hj1 hj2
    simpa [emb] using this
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2
  simp [blockVal] at h0 h1 h2
  exact Prod.ext h0 (Prod.ext h1 h2)

/-- The single-qubit "response function": for two single-qubit operators, `M` at `q` and
`N` at `r`, this is the overlap they produce on a codeword basis state, as a function
of the bit values at `q` and at `r`. -/
