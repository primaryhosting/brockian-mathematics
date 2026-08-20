/-
# Det Eq Mertens 5
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Riemann
namespace Redheffer

/-- The `5 × 5` Redheffer matrix over `ℤ`, with rows and columns indexed by `Fin 5`
(0-indexed): the `(i, j)` entry is `1` if `j = 0` or `(i+1) ∣ (j+1)`, and `0` otherwise. -/

lemma R_eq :
    R = !![1, 1, 1, 1, 1;
           1, 1, 0, 1, 0;
           1, 0, 1, 0, 0;
           1, 0, 0, 1, 0;
           1, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [R]

/-- The determinant of the `5 × 5` Redheffer matrix equals `M(5) = -2`, the Mertens
function at `5`. -/
