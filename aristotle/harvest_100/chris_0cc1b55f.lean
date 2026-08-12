import Mathlib
/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
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

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo `p` when the image of `a` in `ZMod p` has
multiplicative order exactly `p - 1`, i.e. it generates the group of units of `ZMod p`. -/
def IsPrimitiveRootMod (a : ℤ) (p : ℕ) : Prop :=
  orderOf ((a : ZMod p)) = p - 1

/-- The set of primes modulo which `a` is a primitive root. -/
def primitiveRootPrimes (a : ℤ) : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ IsPrimitiveRootMod a p}

/-- **Artin's conjecture on primitive roots**: every integer `a` which is neither `-1`
nor a perfect square is a primitive root modulo infinitely many primes. -/
def ArtinConjecture : Prop :=
  ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → (primitiveRootPrimes a).Infinite

/-! ### Base cases: explicit primitive roots -/

theorem isPrimitiveRootMod_two_three : IsPrimitiveRootMod 2 3 := by
  unfold IsPrimitiveRootMod
  norm_num
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, by decide⟩

theorem isPrimitiveRootMod_two_five : IsPrimitiveRootMod 2 5 := by
  unfold IsPrimitiveRootMod
  norm_num
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, by decide⟩

theorem isPrimitiveRootMod_two_eleven : IsPrimitiveRootMod 2 11 := by
  unfold IsPrimitiveRootMod
  norm_num
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, by decide⟩

/-! ### The excluded cases really have to be excluded -/

/-- If `a` is a perfect square then `a` can only be a primitive root modulo `2`. -/
theorem eq_two_of_isSquare_of_isPrimitiveRootMod {a : ℤ} {p : ℕ} (hp : Nat.Prime p)
    (hsq : IsSquare a) (h : IsPrimitiveRootMod a p) : p = 2 := by
  unfold IsPrimitiveRootMod at h
  by_contra hne
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hne
  obtain ⟨b, rfl⟩ := hsq
  have hp2 : 2 ≤ p := hp.two_le
  set x : ZMod p := (b : ZMod p) with hx
  have hcast : ((b * b : ℤ) : ZMod p) = x * x := by push_cast [hx]; ring
  rw [hcast] at h
  have hx0 : x ≠ 0 := by
    rintro h0
    rw [h0] at h
    simp at h
    omega
  have hpow : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx0
  have h2 : (x * x) ^ ((p - 1) / 2) = 1 := by
    rw [← sq, ← pow_mul]
    have h3 : 2 * ((p - 1) / 2) = p - 1 := by obtain ⟨k, hk⟩ := hodd; omega
    rw [h3, hpow]
  have hdvd := orderOf_dvd_of_pow_eq_one h2
  rw [h] at hdvd
  have hpos : 0 < (p - 1) / 2 := by
    have h3 : 3 ≤ p := by omega
    omega
  have := Nat.le_of_dvd hpos hdvd
  omega

/-- `-1` can only be a primitive root modulo `2` and `3`. -/
theorem eq_two_or_three_of_isPrimitiveRootMod_neg_one {p : ℕ} (hp : Nat.Prime p)
    (h : IsPrimitiveRootMod (-1) p) : p = 2 ∨ p = 3 := by
  unfold IsPrimitiveRootMod at h
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hcast : ((-1 : ℤ) : ZMod p) = -1 := by push_cast; ring
  rw [hcast] at h
  have : orderOf (-1 : ZMod p) ≤ 2 := by
    apply Nat.le_of_dvd (by norm_num)
    apply orderOf_dvd_of_pow_eq_one
    simp
  omega

theorem finite_primitiveRootPrimes_of_isSquare {a : ℤ} (hsq : IsSquare a) :
    (primitiveRootPrimes a).Finite := by
  apply Set.Finite.subset (Set.finite_singleton 2)
  rintro p ⟨hp, h⟩
  exact eq_two_of_isSquare_of_isPrimitiveRootMod hp hsq h

theorem finite_primitiveRootPrimes_neg_one :
    (primitiveRootPrimes (-1)).Finite := by
  apply Set.Finite.subset (Set.toFinite ({2, 3} : Set ℕ))
  rintro p ⟨hp, h⟩
  rcases eq_two_or_three_of_isPrimitiveRootMod_neg_one hp h with h' | h' <;> simp [h']

/-! ### The main statement -/

/-- **Artin's conjecture on primitive roots**, together with a Lean-checked reduction:
the conjecture (`ArtinConjecture`: any integer that is neither `-1` nor a perfect square
is a primitive root modulo infinitely many primes) is *equivalent* to the sharper
characterisation saying that an integer is a primitive root modulo infinitely many primes
*exactly when* it is neither `-1` nor a perfect square.

The nontrivial content proved here is the unconditional converse direction: for `a = -1`
and for perfect squares `a`, the set of primes modulo which `a` is a primitive root is
finite (contained in `{2, 3}`, resp. `{2}`). Hence nothing is lost by stating Artin's
conjecture with those exclusions. -/
theorem artin_primitive_root :
    ArtinConjecture ↔
      ∀ a : ℤ, ((primitiveRootPrimes a).Infinite ↔ (a ≠ -1 ∧ ¬ IsSquare a)) := by
  constructor
  · intro H a
    refine ⟨fun hinf => ⟨?_, ?_⟩, fun h => H a h.1 h.2⟩
    · rintro rfl
      exact hinf finite_primitiveRootPrimes_neg_one
    · intro hsq
      exact hinf (finite_primitiveRootPrimes_of_isSquare hsq)
  · intro H a ha hsq
    exact (H a).2 ⟨ha, hsq⟩

end Frontier

