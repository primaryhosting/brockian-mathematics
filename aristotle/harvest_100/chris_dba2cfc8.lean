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
theorem card_units_zmod (n : ℕ) [NeZero n] :
    Fintype.card (ZMod n)ˣ = Nat.totient n := by
  haveI : Fact (0 < n) := ⟨Nat.pos_of_ne_zero (NeZero.ne n)⟩
  exact ZMod.card_units_eq_totient n

/-- Euler's theorem, unit-group form: any unit of `ZMod n` raised to the power
`Nat.totient n` is `1`. -/
theorem euler_totient_units {n : ℕ} [NeZero n] (u : (ZMod n)ˣ) :
    u ^ Nat.totient n = 1 := by
  rw [← card_units_zmod n]
  exact pow_card_eq_one

/-- **Euler's theorem**: if `a : ZMod n` is a unit, then `a ^ Nat.totient n = 1`. -/
theorem euler_totient {n : ℕ} {a : ZMod n} (ha : IsUnit a) :
    a ^ Nat.totient n = 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · haveI : NeZero n := ⟨hn⟩
    obtain ⟨u, rfl⟩ := ha
    rw [← Units.val_pow_eq_pow_val, euler_totient_units u, Units.val_one]

/-- **Euler's theorem**, congruence form: if `a` and `n` are coprime natural numbers,
then `a ^ Nat.totient n ≡ 1 [MOD n]`. -/
theorem euler_totient_nat {a n : ℕ} (h : Nat.Coprime a n) :
    a ^ Nat.totient n ≡ 1 [MOD n] := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Nat.ModEq]
  · haveI : NeZero n := ⟨hn⟩
    have hu : IsUnit (a : ZMod n) := (ZMod.isUnit_iff_coprime a n).2 h
    have := euler_totient hu
    have : ((a ^ Nat.totient n : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
      push_cast
      exact this
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 this

/-! ### A self-contained proof, not using Lagrange's theorem

The following gives an independent route to Euler's theorem: in a finite commutative
group, multiplication by a fixed element permutes the group, so comparing the product
of all elements with the product of all their translates yields `u ^ card = 1`.
-/

/-- In a finite commutative group, every element raised to the order of the group is `1`.
Proved directly by the "multiply-everything" (permutation of the group) argument. -/
theorem pow_card_eq_one_of_comm {G : Type*} [CommGroup G] [Fintype G] (u : G) :
    u ^ Fintype.card G = 1 := by
  have hperm : ∏ x : G, (u * x) = ∏ x : G, x :=
    Equiv.prod_comp (Equiv.mulLeft u) (fun x => x)
  have hsplit : ∏ x : G, (u * x) = u ^ Fintype.card G * ∏ x : G, x := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have : u ^ Fintype.card G * ∏ x : G, x = 1 * ∏ x : G, x := by
    rw [one_mul, ← hsplit, hperm]
  exact mul_right_cancel this

/-- **Euler's theorem** again, proved without invoking Lagrange's theorem: the argument
goes through the permutation-of-units product identity `pow_card_eq_one_of_comm`. -/
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

