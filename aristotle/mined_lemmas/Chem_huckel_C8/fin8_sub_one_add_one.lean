/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real Matrix SimpleGraph

namespace Chem

/-- The adjacency matrix (over `ℝ`) of the cycle graph `C₈`, i.e. the Hückel matrix of
cyclooctatetraene in units where `α = 0` and `β = 1`. -/

lemma fin8_sub_one_add_one (i : Fin 8) : i - 1 + 1 = i := by revert i; decide
