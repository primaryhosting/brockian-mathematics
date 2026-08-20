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

lemma two_cos_two : 2 * Real.cos (2 * Real.pi * ((2 : ℕ) : ℝ) / 3) = -1 := huckelLevelC3_two

/-- **Hückel theory for the cyclopropenyl system (C₃).**
The characteristic polynomial of the adjacency matrix of the cycle graph `C₃` factors as
`∏_{k=0}^{2} (X - 2 cos (2πk/3))`; consequently the spectrum (set of eigenvalues) of the
adjacency matrix is exactly the set of Hückel levels `2 cos (2πk/3)` for `k = 0, 1, 2`
(namely `2, -1, -1`). -/
