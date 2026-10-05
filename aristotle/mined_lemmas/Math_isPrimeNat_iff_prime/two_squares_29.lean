import Mathlib
import RequestProject.TwoSquares29

/-!
Mathlib-facing restatement of `Math.two_squares_29`: the predicate `Math.IsPrimeNat` used in
`RequestProject/TwoSquares29.lean` agrees with Mathlib's `Nat.Prime`, so `29` is a Mathlib-prime
which is a sum of two squares.
-/

namespace Math


theorem two_squares_29 : IsPrimeNat 29 ∧ ∃ a b : Nat, 29 = a ^ 2 + b ^ 2 :=
  ⟨isPrimeNat_29, 2, 5, by decide⟩

end Math

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

