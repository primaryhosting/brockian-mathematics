/-
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
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

namespace NumberTheory

/-- **Euler's theorem**, unit-group form: any unit of `ZMod n` raised to the power
`Nat.totient n` is `1`.  For `n > 0` this is Lagrange's theorem applied to the group
`(ZMod n)ˣ`, whose cardinality is `Nat.totient n`; for `n = 0` the exponent is `0`. -/

theorem euler_totient_int {a : ℤ} {n : ℕ} (h : IsCoprime a (n : ℤ)) :
    a ^ Nat.totient n ≡ 1 [ZMOD (n : ℤ)] := by
  have hu : IsUnit ((a : ZMod n)) := (ZMod.coe_int_isUnit_iff_isCoprime a n).2 h.symm
  have h2 := euler_totient hu
  exact (ZMod.intCast_eq_intCast_iff _ _ _).1 (by push_cast; simpa using h2)

end NumberTheory

#print axioms NumberTheory.euler_totient
#print axioms NumberTheory.euler_totient_nat
#print axioms NumberTheory.euler_totient_int

