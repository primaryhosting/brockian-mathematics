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

/-!
# Bezout
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.bezout
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace NumberTheory

/-- **Bézout's identity** for the integers: for all integers `a` and `b` there exist
integers `x` and `y` with `a * x + b * y = Int.gcd a b`.

The proof uses Mathlib's `Int.gcd_eq_gcd_ab`, which states
`(Int.gcd a b : ℤ) = a * Int.gcdA a b + b * Int.gcdB a b`, where `Int.gcdA`/`Int.gcdB`
are the Bézout coefficients produced by the extended Euclidean algorithm. -/
theorem bezout (a b : ℤ) : ∃ x y : ℤ, a * x + b * y = (Int.gcd a b : ℤ) :=
  ⟨Int.gcdA a b, Int.gcdB a b, (Int.gcd_eq_gcd_ab a b).symm⟩

end NumberTheory

