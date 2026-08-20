/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Polynomial SimpleGraph

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₄`. -/

lemma C14vand_isUnit : IsUnit C14vand :=
  (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 C14vand_det_ne_zero)

