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

lemma C7_row_sum (i : Fin 7) : ∑ j, C7 i j = 2 := by
  simp only [C7, Fin.sum_univ_seven]
  fin_cases i <;> simp +decide <;> norm_num

/-- The adjacency matrix of `C₇`, viewed over `ℂ`. -/
