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

lemma C7_transpose : C7ᵀ = C7 := by
  ext i j
  simp only [Matrix.transpose_apply, C7]
  exact if_congr or_comm rfl rfl

/-- Every vertex of `C₇` has degree `2`. -/
