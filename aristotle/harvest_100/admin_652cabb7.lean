import Mathlib
/-!
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- **Euler's theorem**, unit-group form: for a unit `u` of `ZMod n`,
`u ^ φ n = 1`.  This is the statement that the group of units of `ZMod n` has
order `φ n`, combined with Lagrange's theorem. -/
theorem euler_totient_units {n : ℕ} [NeZero n] (u : (ZMod n)ˣ) :
    u ^ Nat.totient n = 1 := by
  have hcard : Fintype.card (ZMod n)ˣ = Nat.totient n := ZMod.card_units_eq_totient n
  have h := pow_card_eq_one (G := (ZMod n)ˣ) (x := u)
  rwa [hcard] at h

/-- **Euler's theorem** for `ZMod n`: if `a : ZMod n` is a unit then
`a ^ φ n = 1`. -/
theorem euler_totient {n : ℕ} {a : ZMod n} (ha : IsUnit a) :
    a ^ Nat.totient n = 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · haveI : NeZero n := ⟨hn⟩
    obtain ⟨u, rfl⟩ := ha
    rw [← Units.val_pow_eq_pow_val, euler_totient_units u, Units.val_one]

/-- **Euler's theorem**, congruence form: if `a` and `n` are coprime natural numbers,
then `a ^ φ n ≡ 1 [MOD n]`. -/
theorem euler_totient_modEq {a n : ℕ} (h : Nat.Coprime a n) :
    a ^ Nat.totient n ≡ 1 [MOD n] := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Nat.ModEq]
  · haveI : NeZero n := ⟨hn⟩
    have hu : IsUnit (a : ZMod n) := (ZMod.isUnit_iff_coprime a n).2 h
    have hz : ((a ^ Nat.totient n : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
      push_cast
      simpa using euler_totient hu
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hz

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

