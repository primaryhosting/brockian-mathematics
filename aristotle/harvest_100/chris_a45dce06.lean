/-
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace NumberTheory

/-- Euler's theorem, `ZMod` form: any unit `a` of `ZMod n` satisfies
`a ^ Nat.totient n = 1`. -/
theorem euler_totient_zmod {n : ℕ} (a : ZMod n) (ha : IsUnit a) :
    a ^ Nat.totient n = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have : u ^ Nat.totient n = 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- `ZMod 0 = ℤ`, totient 0 = 0
      simp
    · haveI : NeZero n := ⟨hn.ne'⟩
      rw [← ZMod.card_units_eq_totient n]
      exact pow_card_eq_one
  rw [← Units.val_pow_eq_pow_val, this, Units.val_one]

/-- Euler's theorem, integer/`Nat` form: if `a` and `n` are coprime then
`a ^ Nat.totient n ≡ 1 [MOD n]`. -/
theorem euler_totient {a n : ℕ} (h : Nat.Coprime a n) :
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

