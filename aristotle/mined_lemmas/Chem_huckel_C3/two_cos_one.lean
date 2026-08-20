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

lemma two_cos_one : 2 * Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) / 3) = -1 := huckelLevelC3_one

