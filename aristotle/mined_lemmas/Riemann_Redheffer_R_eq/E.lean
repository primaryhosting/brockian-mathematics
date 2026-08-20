import Mathlib

/-!
# Det Eq Mertens 6
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_6
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Riemann.Redheffer

/-- The `6 × 6` Redheffer matrix: with `Fin 6` indices `i, j` standing for the
divisor `i + 1` and the integer `j + 1`, the entry is `1` when `j = 0`
(the first column) or when `i + 1` divides `j + 1`, and `0` otherwise. -/

def E : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ 1, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0;
     -1, 0, 0, 1, 0, 0;
     -1, 0, 0, 0, 1, 0;
     -1, 0, 0, 0, 0, 1]

/-- The upper triangular matrix obtained from `R` by the column operation `E`. -/
