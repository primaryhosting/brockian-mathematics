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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false


theorem oppermann_check_le_200 :
    (List.range 201).all
      (fun n => decide (n < 2) ||
        (hasPrimeIn (n * (n - 1)) (n * n) && hasPrimeIn (n * n) (n * (n + 1)))) = true := by
  decide

/-- Unconditional partial result: Oppermann's conjecture holds for `1 < n ≤ 200`. -/
