import Mathlib

namespace Frontier

/-- 42 as a sum of three cubes (Booker–Sutherland solution). -/

theorem sum_three_cubes_42 :
    (42 : ℤ) = (-80538738812075974)^3 + 80435758145817515^3 + 12602123297335631^3 := by
  norm_num

end Frontier

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

