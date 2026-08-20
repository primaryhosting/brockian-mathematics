/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Real Matrix SimpleGraph

namespace Chem

/-- The Hückel level of the `k`-th molecular orbital of the cyclic `C₃` system,
in units of the resonance integral `β` (relative to `α`): `2 cos (2πk/3)`. -/

lemma huckelLevelC3_zero : huckelLevelC3 0 = 2 := by
  simp [huckelLevelC3]

