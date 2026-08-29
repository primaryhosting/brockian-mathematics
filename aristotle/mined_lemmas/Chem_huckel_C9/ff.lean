/-
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open Complex Polynomial SimpleGraph

namespace Chem

/-- A primitive `9`-th root of unity. -/

noncomputable def ff (m : ZMod 9) : ℂ := zeta ^ m.val

/-- The adjacency matrix of the cycle graph `C₉`, viewed over the index type `ZMod 9`
(which is definitionally `Fin 9`). -/
