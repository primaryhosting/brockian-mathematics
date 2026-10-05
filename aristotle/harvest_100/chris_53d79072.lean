/-!
# Sum Three Cubes 42
Category: Frontier — Prime Numbers
Target: Frontier.sum_three_cubes_42
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The Booker–Sutherland representation of `42` as a sum of three integer cubes:
`42 = (-80538738812075974)³ + 80435758145817515³ + 12602123297335631³`. -/
theorem sum_three_cubes_42 :
    (42 : Int) =
      (-80538738812075974) ^ 3 + 80435758145817515 ^ 3 + 12602123297335631 ^ 3 := by
  decide

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

