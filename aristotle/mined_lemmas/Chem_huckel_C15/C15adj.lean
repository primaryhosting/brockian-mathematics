/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset

/-- A primitive 15-th root of unity. -/

noncomputable def C15adj : Matrix (ZMod 15) (ZMod 15) ℂ :=
  Matrix.of fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

