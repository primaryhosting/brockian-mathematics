/-
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace NumberTheory

open Nat

/-- **Euler's theorem**, unit-group form: for every unit `x` of `ZMod n`,
`x ^ φ n = 1`. This is Mathlib's `ZMod.pow_totient`. -/

theorem euler_totient_int {a : ℤ} {n : ℕ} (h : IsCoprime a (n : ℤ)) :
    (n : ℤ) ∣ a ^ Nat.totient n - 1 := by
  have hu : IsUnit (a : ZMod n) := by
    rcases h with ⟨u, v, huv⟩
    have hmul : (a : ZMod n) * (u : ZMod n) = 1 := by
      have : ((u * a + v * n : ℤ) : ZMod n) = ((1 : ℤ) : ZMod n) := by rw [huv]
      push_cast at this
      simpa [mul_comm] using this
    exact IsUnit.of_mul_eq_one _ hmul
  have hpow := euler_totient hu
  have hzero : ((a ^ Nat.totient n - 1 : ℤ) : ZMod n) = 0 := by
    push_cast
    rw [hpow]
    ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp hzero

#print axioms euler_totient
#print axioms euler_totient_units
#print axioms euler_totient_modEq
#print axioms euler_totient_int

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

