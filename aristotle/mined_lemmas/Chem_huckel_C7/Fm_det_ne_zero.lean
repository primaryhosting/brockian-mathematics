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

lemma Fm_det_ne_zero : Fm.det ≠ 0 := by
  rw [Fm, Matrix.det_vandermonde_ne_zero_iff]
  intro i j hij
  exact Fin.ext (w_primitive.pow_inj i.isLt j.isLt hij)

/-- The Fourier matrix diagonalizes the circulant adjacency matrix of `C₇`. -/
