/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Matrix
open Complex

namespace Chem

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₀`. -/

lemma pow_shift_eq (z : ℂ) (h10 : z ^ 10 = 1) (i : Fin 10) :
    z ^ ((i - 1 : Fin 10) : ℕ) + z ^ ((i + 1 : Fin 10) : ℕ) = z ^ (i : ℕ) * (z + z ^ 9) := by
  fin_cases i <;> norm_num [Fin.sub_def, Fin.add_def] <;>
    first
      | ring1
      | linear_combination (-1 : ℂ) * h10
      | linear_combination (-z) * h10
      | linear_combination (-z ^ 2) * h10
      | linear_combination (-z ^ 3) * h10
      | linear_combination (-z ^ 4) * h10
      | linear_combination (-z ^ 5) * h10
      | linear_combination (-z ^ 6) * h10
      | linear_combination (-z ^ 7) * h10
      | linear_combination (-1 - z ^ 8) * h10

