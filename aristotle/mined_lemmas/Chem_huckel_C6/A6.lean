import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix of the cycle graph `C₆`, written out explicitly. -/

def A6 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 1, 0, 0, 0, 1;
     1, 0, 1, 0, 0, 0;
     0, 1, 0, 1, 0, 0;
     0, 0, 1, 0, 1, 0;
     0, 0, 0, 1, 0, 1;
     1, 0, 0, 0, 1, 0]

/-- The Hückel energies (adjacency eigenvalues) of `C₆`, in the order `k = 0,…,5`,
i.e. `2 cos (2πk/6)`. -/
