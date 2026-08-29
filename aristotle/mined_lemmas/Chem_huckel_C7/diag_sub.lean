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

lemma diag_sub (μ : ℂ) :
    Matrix.diagonal (fun k : Fin 7 => ((ev k : ℝ) : ℂ)) - μ • (1 : Matrix (Fin 7) (Fin 7) ℂ)
      = Matrix.diagonal (fun k : Fin 7 => ((ev k : ℝ) : ℂ) - μ) := by
  ext i j
  by_cases h : i = j <;> simp [h]

/-- The characteristic determinant of the adjacency matrix of `C₇` factors completely. -/
