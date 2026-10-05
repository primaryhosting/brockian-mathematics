/-
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace NumberTheory

/-- **Euler's theorem**, unit-group form: for a unit `u` of `ZMod n`,
`u ^ Nat.totient n = 1`. -/
theorem euler_totient_units (n : ℕ) (u : (ZMod n)ˣ) : u ^ Nat.totient n = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `(ZMod 0)ˣ = ℤˣ` and `Nat.totient 0 = 0`
    simp
  · haveI : NeZero n := ⟨hn.ne'⟩
    have hcard : Fintype.card (ZMod n)ˣ = Nat.totient n := ZMod.card_units_eq_totient n
    rw [← hcard]
    exact pow_card_eq_one

/-- **Euler's theorem**: if `a : ZMod n` is a unit, then `a ^ Nat.totient n = 1`. -/
theorem euler_totient {n : ℕ} {a : ZMod n} (ha : IsUnit a) : a ^ Nat.totient n = 1 := by
  obtain ⟨u, rfl⟩ := ha
  rw [← Units.val_pow_eq_pow_val, euler_totient_units n u, Units.val_one]

/-- If `a` is coprime to `n`, then `(a : ZMod n)` is a unit. -/
theorem isUnit_natCast_of_coprime {a n : ℕ} (h : Nat.Coprime a n) : IsUnit (a : ZMod n) :=
  (ZMod.isUnit_iff_coprime a n).2 h

/-- **Euler's theorem**, congruence form: if `a` and `n` are coprime, then
`a ^ Nat.totient n ≡ 1 [MOD n]`.  Derived from `euler_totient` above. -/
theorem euler_totient_modEq {a n : ℕ} (h : Nat.Coprime a n) :
    a ^ Nat.totient n ≡ 1 [MOD n] := by
  have hz : ((a ^ Nat.totient n : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
    push_cast
    exact euler_totient (isUnit_natCast_of_coprime h)
  exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hz

/-- **Fermat's little theorem** as a corollary: if `p` is prime and `p ∤ a`, then
`a ^ (p - 1) ≡ 1 [MOD p]`. -/
theorem fermat_little_of_euler {p a : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  have hcop : Nat.Coprime a p := ((Nat.Prime.coprime_iff_not_dvd hp).2 ha).symm
  simpa [Nat.totient_prime hp] using euler_totient_modEq hcop

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

