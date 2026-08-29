/- (Lean requires `import` to precede any module docstring `/-! ... -/`, so this header
is given as a plain block comment.)
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Complex Real

/-- The adjacency matrix of the cycle graph `C₇`, with vertices indexed by `Fin 7`
(where addition is modulo `7`): vertices `i` and `j` are adjacent iff they differ by one
step around the cycle. -/

lemma C7C_mul_Fm : C7C * Fm = Fm * Matrix.diagonal (fun k : Fin 7 => ((ev k : ℝ) : ℂ)) := by
  ext i k
  rw [Matrix.mul_diagonal, ev_eq]
  have hF : ∀ j : Fin 7, Fm j k = (w ^ (k : ℕ)) ^ (j : ℕ) := by
    intro j; simp [Fm, Matrix.vandermonde_apply, ← pow_mul, Nat.mul_comm]
  have h7 : (w ^ (k : ℕ)) ^ 7 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, w_pow_seven, one_pow]
  have hinv : (w ^ (k : ℕ))⁻¹ = (w ^ (k : ℕ)) ^ 6 :=
    inv_eq_of_mul_eq_one_right (by linear_combination h7)
  rw [Matrix.mul_apply, hinv]
  simp only [Fin.sum_univ_seven, hF, C7C]
  set x := w ^ (k : ℕ) with hxdef
  clear_value x
  fin_cases i <;> simp +decide
  · linear_combination -h7
  · linear_combination -x * h7
  · linear_combination -x ^ 2 * h7
  · linear_combination -x ^ 3 * h7
  · linear_combination -x ^ 4 * h7
  · linear_combination -(1 + x ^ 5) * h7

