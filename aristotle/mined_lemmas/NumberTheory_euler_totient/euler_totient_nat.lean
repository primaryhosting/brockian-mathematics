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

theorem euler_totient_nat {a n : ℕ} (h : Nat.Coprime a n) :
    a ^ Nat.totient n ≡ 1 [MOD n] := by
  have hu : IsUnit ((a : ZMod n)) := (ZMod.isUnit_iff_coprime a n).2 h
  have h2 := euler_totient hu
  exact (ZMod.natCast_eq_natCast_iff (a ^ Nat.totient n) 1 n).1 (by push_cast; simpa using h2)

/-- **Euler's theorem**, congruence form over `ℤ`: if `a` and `n` are coprime then
`a ^ Nat.totient n ≡ 1 [ZMOD n]`. -/
