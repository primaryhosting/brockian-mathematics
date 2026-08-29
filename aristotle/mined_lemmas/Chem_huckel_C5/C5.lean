/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace Chem

open Matrix

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
in units where the Coulomb integral `α` is `0` and the resonance integral `β` is `1`). -/

def C5 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 1, 0, 0, 1;
     1, 0, 1, 0, 0;
     0, 1, 0, 1, 0;
     0, 0, 1, 0, 1;
     1, 0, 0, 1, 0]

/-- `C₅`'s adjacency matrix satisfies its minimal polynomial `x³ - x² - 3x + 2`. -/
