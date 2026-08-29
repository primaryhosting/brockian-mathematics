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

lemma ipf_adjoint (E F : Matrix Bits Bits ℂ) (u v : Amp) :
    ipf u ((Eᴴ * F).mulVec v) = ipf (E.mulVec u) (F.mulVec v) := by
  have hL : ipf u ((Eᴴ * F).mulVec v)
      = ∑ b : Bits, ∑ d : Bits, ∑ c : Bits,
          star (u b) * star (E c b) * F c d * v d := by
    simp only [ipf, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
      starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ =>
      Finset.sum_congr rfl fun c _ => by ring
  have hR : ipf (E.mulVec u) (F.mulVec v)
      = ∑ c : Bits, ∑ d : Bits, ∑ b : Bits,
          star (u b) * star (E c b) * F c d * v d := by
    simp only [ipf, Matrix.mulVec, dotProduct, starRingEnd_apply, star_sum, star_mul',
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
      Finset.sum_congr rfl fun b _ => by ring
  rw [hL, hR, sum_swap3]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- **The Shor code corrects an arbitrary single-qubit error.**

This is the Knill–Laflamme error-correction condition for the nine-qubit Shor code: for any
two errors `E`, `F` each acting arbitrarily on a single (possibly different) qubit, the matrix
of `Eᴴ * F` on the two-dimensional code space spanned by `|0_L⟩`, `|1_L⟩` is a scalar
multiple of the identity.  Equivalently, no such error leaks any information about the encoded
logical state, and a recovery operation exists. -/
