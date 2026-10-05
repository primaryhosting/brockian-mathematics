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

lemma real_det_eq (μ : ℝ) :
    ((C7 - μ • (1 : Matrix (Fin 7) (Fin 7) ℝ)).det : ℂ)
      = (C7C - (μ : ℂ) • (1 : Matrix (Fin 7) (Fin 7) ℂ)).det := by
  rw [show ((C7 - μ • (1 : Matrix (Fin 7) (Fin 7) ℝ)).det : ℂ)
      = Complex.ofRealHom ((C7 - μ • (1 : Matrix (Fin 7) (Fin 7) ℝ)).det) from rfl,
    RingHom.map_det, map_C7_sub]

/-- **Hückel theory for the cycle `C₇`.**  A real number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₇` if and only if `μ = 2 cos (2πk/7)` for some
`k ∈ {0, 1, …, 6}`. -/
