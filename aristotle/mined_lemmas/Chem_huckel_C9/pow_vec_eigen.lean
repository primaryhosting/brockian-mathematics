import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SimpleGraph Matrix

namespace Chem

/-- The primitive 9-th root of unity `exp (2πi/9)`. -/

lemma pow_vec_eigen (W : ℂ) (hW : W ^ 9 = 1) (i : Fin 9) :
    W ^ ((i - 1 : Fin 9) : ℕ) + W ^ ((i + 1 : Fin 9) : ℕ) = (W + W ^ 8) * W ^ (i : ℕ) := by
  fin_cases i
  · show W ^ (8 : ℕ) + W ^ (1 : ℕ) = (W + W ^ 8) * W ^ (0 : ℕ); ring
  · show W ^ (0 : ℕ) + W ^ (2 : ℕ) = (W + W ^ 8) * W ^ (1 : ℕ); linear_combination -hW
  · show W ^ (1 : ℕ) + W ^ (3 : ℕ) = (W + W ^ 8) * W ^ (2 : ℕ); linear_combination -W * hW
  · show W ^ (2 : ℕ) + W ^ (4 : ℕ) = (W + W ^ 8) * W ^ (3 : ℕ); linear_combination -W ^ 2 * hW
  · show W ^ (3 : ℕ) + W ^ (5 : ℕ) = (W + W ^ 8) * W ^ (4 : ℕ); linear_combination -W ^ 3 * hW
  · show W ^ (4 : ℕ) + W ^ (6 : ℕ) = (W + W ^ 8) * W ^ (5 : ℕ); linear_combination -W ^ 4 * hW
  · show W ^ (5 : ℕ) + W ^ (7 : ℕ) = (W + W ^ 8) * W ^ (6 : ℕ); linear_combination -W ^ 5 * hW
  · show W ^ (6 : ℕ) + W ^ (8 : ℕ) = (W + W ^ 8) * W ^ (7 : ℕ); linear_combination -W ^ 6 * hW
  · show W ^ (7 : ℕ) + W ^ (0 : ℕ) = (W + W ^ 8) * W ^ (8 : ℕ)
    linear_combination (-(1 + W ^ 7)) * hW

/-- Every complex number is of the form `z + z⁻¹` for some nonzero `z`. -/
