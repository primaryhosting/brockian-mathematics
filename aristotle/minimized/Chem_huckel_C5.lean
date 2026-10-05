/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Matrix Real

namespace Chem

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
with `α = 0`, `β = 1`), with vertices `0,1,2,3,4` arranged in a pentagon. -/

noncomputable def C5adj : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0,1,0,0,1; 1,0,1,0,0; 0,1,0,1,0; 0,0,1,0,1; 1,0,0,1,0]

set_option maxHeartbeats 2000000 in
/-- The characteristic identity `A⁵ = 5A³ - 5A + 2I` satisfied by the adjacency matrix
of `C₅` (Cayley–Hamilton for the characteristic polynomial `x⁵ - 5x³ + 5x - 2`). -/
