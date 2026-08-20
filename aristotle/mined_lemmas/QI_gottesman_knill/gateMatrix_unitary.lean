/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain comment and is repeated as a docstring below.)

import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace QI

/-! ## Phases and signs -/

/-- Computational basis labels for `n` qubits: bit strings of length `n`. -/
abbrev Bits (n : ℕ) : Type := Fin n → ZMod 2

/-- The fourth root of unity `i ^ s` attached to `s : ZMod 4`. -/

lemma gateMatrix_unitary {n : ℕ} (g : Gate n) : gateMatrix g * (gateMatrix g)ᴴ = 1 := by
  cases g with
  | H q =>
      rw [gateMatrix, tp_conjTranspose, tp_mul]
      rw [show (fun r => Function.update (fun _ => (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) q hmat r *
          (Function.update (fun _ => (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) q hmat r)ᴴ)
          = fun _ : Fin n => (1 : Matrix (ZMod 2) (ZMod 2) ℂ) from ?_]
      · exact tp_one
      · funext r
        by_cases hr : r = q
        · subst hr; simpa using hmat_unitary
        · simp [Function.update_of_ne hr]
  | S q =>
      rw [gateMatrix, tp_conjTranspose, tp_mul]
      rw [show (fun r => Function.update (fun _ => (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) q smat r *
          (Function.update (fun _ => (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) q smat r)ᴴ)
          = fun _ : Fin n => (1 : Matrix (ZMod 2) (ZMod 2) ℂ) from ?_]
      · exact tp_one
      · funext r
        by_cases hr : r = q
        · subst hr; simpa using smat_unitary
        · simp [Function.update_of_ne hr]
  | CZ c t =>
      rw [gateMatrix, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
        ← Matrix.diagonal_one]
      congr 1
      funext a
      simp only [Pi.mul_apply, Pi.star_apply, Pi.one_apply, Complex.star_def, conj_psign]
      rcases zmod2_cases (a c * a t) with h | h <;> simp [psign, h]

