import Mathlib

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

open Matrix

/-- The adjacency matrix of the cycle graph `C₆`, written out explicitly. -/

def B6 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![2,0,1,0,1,0;
     0,2,0,1,0,1;
     1,0,2,0,1,0;
     0,1,0,2,0,1;
     1,0,1,0,2,0;
     0,1,0,1,0,2]

/-- The adjacency matrix of Mathlib's `cycleGraph 6` is `A6`. -/
