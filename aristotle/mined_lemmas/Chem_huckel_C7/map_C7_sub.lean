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

lemma map_C7_sub (μ : ℝ) :
    (Complex.ofRealHom).mapMatrix (C7 - μ • (1 : Matrix (Fin 7) (Fin 7) ℝ))
      = C7C - (μ : ℂ) • (1 : Matrix (Fin 7) (Fin 7) ℂ) := by
  rw [map_sub, map_C7]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h]

