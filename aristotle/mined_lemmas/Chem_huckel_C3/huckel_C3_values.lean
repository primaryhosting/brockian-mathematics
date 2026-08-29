/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Real Matrix

/-- The adjacency matrix of the cycle graph `C₃` (the complete graph on 3 vertices):
zero on the diagonal, one off the diagonal. -/

lemma huckel_C3_values (k : Fin 3) :
    2 * Real.cos (2 * Real.pi * (k : ℕ) / 3) = if k = 0 then 2 else -1 := by
  fin_cases k
  · norm_num
  · norm_num
    rw [cos_two_pi_div_three]
    norm_num
  · norm_num
    rw [show (2 : ℝ) * Real.pi * 2 / 3 = 4 * Real.pi / 3 by ring, cos_four_pi_div_three]
    norm_num

/-- **Hückel theory for `C₃`.** A real number `μ` is an eigenvalue of the adjacency matrix of
the cycle graph `C₃` if and only if it is of the form `2 cos(2πk/3)` for some `k = 0, 1, 2`. -/
