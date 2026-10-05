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

lemma G_zeroL_oneL_formula (Z : Bits) :
    G 0 Z zeroL oneL
      = kappa * kappa * ∑ c : Fin 3 → ZMod 2, sgn (dot Z (rep c) + lw (rep c)) := by
  rw [G]
  rw [sum_over_code _ (fun b hb => by simp [zeroL_off hb])]
  have : ∀ c : Fin 3 → ZMod 2,
      sgn (dot Z (rep c)) * ((starRingEnd ℂ) (zeroL (rep c)) * oneL (rep c + 0))
        = kappa * kappa * sgn (dot Z (rep c) + lw (rep c)) := by
    intro c
    simp only [add_zero, zeroL, oneL, if_pos (isCode_rep c), conj_kappa, sgn_add]
    ring
  simp only [this, ← Finset.mul_sum]

