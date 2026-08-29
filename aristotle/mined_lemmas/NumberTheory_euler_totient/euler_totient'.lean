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


namespace NumberTheory

/-- The group of units of `ZMod n` has order `Nat.totient n`, for `n > 0`. -/

theorem euler_totient' {n : ℕ} {a : ZMod n} (ha : IsUnit a) :
    a ^ Nat.totient n = 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · haveI : NeZero n := ⟨hn⟩
    obtain ⟨u, rfl⟩ := ha
    have : u ^ Nat.totient n = 1 := by
      rw [← card_units_zmod n]
      exact pow_card_eq_one_of_comm u
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]

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

