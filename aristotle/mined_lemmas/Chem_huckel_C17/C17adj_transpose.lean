/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Complex

/-! ### A primitive 17-th root of unity and the associated additive character -/

/-- A primitive 17-th root of unity. -/

lemma C17adj_transpose : C17adj.transpose = C17adj := by
  funext i j
  simp only [Matrix.transpose_apply, C17adj, Matrix.of_apply]
  congr 1
  exact propext (or_comm)

/-- Every vertex of `C₁₇` has exactly two neighbours, so `C17adj` really is the adjacency
matrix of a `17`-cycle. -/
