/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command, so the header above is written as a
-- plain block comment rather than a `/-!` module docstring.)

import Mathlib

open scoped BigOperators
open scoped Matrix

namespace QI

/-! ## The 9-qubit register

We label the nine qubits by `Site = Fin 3 × Fin 3`: the first coordinate is the *block*
(one of three three-qubit repetition blocks) and the second the position inside the block.
A computational basis state is a bit string `Bits = Site → ZMod 2`, and a state vector is
its amplitude function `Amp = Bits → ℂ`.
-/

abbrev Site : Type := Fin 3 × Fin 3

abbrev Bits : Type := Site → ZMod 2

abbrev Amp : Type := Bits → ℂ

/-- The Hermitian inner product `⟪u, v⟫ = ∑_b conj (u b) * v b`. -/

lemma dot_allOnes_rep (c : Fin 3 → ZMod 2) : dot allOnes (rep c) = lw (rep c) := by
  rw [dot_rep, lw_rep]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h1 : (∑ _s : Fin 3, allOnes ((r, _s) : Site)) = 1 := by
    simp only [allOnes, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    decide
  rw [h1, one_mul]

/-- `Z^{⊗ 9}` is a logical bit flip on the Shor code: `⟨0_L| Z^{⊗ 9} |1_L⟩ = 1`. -/
