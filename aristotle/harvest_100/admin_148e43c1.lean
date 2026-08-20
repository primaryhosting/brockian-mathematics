import Mathlib
/-!
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- **Euler's theorem** (Fermat–Euler totient theorem): if `a : ZMod n` is a unit, then
`a ^ Nat.totient n = 1`.  This is the `ZMod`-element form of Mathlib's `ZMod.pow_totient`
(which is stated for `x : (ZMod n)ˣ`). -/
theorem euler_totient {n : ℕ} {a : ZMod n} (ha : IsUnit a) : a ^ Nat.totient n = 1 := by
  obtain ⟨u, rfl⟩ := ha
  rw [← Units.val_pow_eq_pow_val, ZMod.pow_totient u, Units.val_one]

/-- **Euler's theorem**, units form: every unit of `ZMod n` has order dividing `φ n`.
This is exactly Mathlib's `ZMod.pow_totient`. -/
theorem euler_totient_units {n : ℕ} (u : (ZMod n)ˣ) : u ^ Nat.totient n = 1 :=
  ZMod.pow_totient u

/-- **Euler's theorem**, congruence form: if `a` and `n` are coprime natural numbers then
`a ^ φ n ≡ 1 [MOD n]`.  This is Mathlib's `Nat.ModEq.pow_totient`. -/
theorem euler_totient_modEq {a n : ℕ} (h : Nat.Coprime a n) :
    a ^ Nat.totient n ≡ 1 [MOD n] :=
  Nat.ModEq.pow_totient h

end NumberTheory

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

