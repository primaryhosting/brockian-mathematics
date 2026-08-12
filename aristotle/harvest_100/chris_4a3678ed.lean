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

/-
# Bezout
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.bezout
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bezout
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.bezout
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- **Bézout's identity** for the integers: for any integers `a` and `b` there exist
integers `x` and `y` with `a * x + b * y = Int.gcd a b`.

The witnesses are Mathlib's extended-Euclidean coefficients `Int.gcdA` and `Int.gcdB`,
and the identity is `Int.gcd_eq_gcd_ab`. -/
theorem bezout (a b : Int) : ∃ x y : Int, a * x + b * y = (Int.gcd a b : Int) :=
  ⟨Int.gcdA a b, Int.gcdB a b, (Int.gcd_eq_gcd_ab a b).symm⟩

end NumberTheory

