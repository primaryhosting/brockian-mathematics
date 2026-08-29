/-
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

set_option maxRecDepth 100000

/-- `a : ℤ` is a *primitive root modulo `p`* when its residue class generates the
multiplicative group of `ZMod p`, i.e. its multiplicative order is `p - 1`. -/
def IsPrimitiveRootMod (a : ℤ) (p : ℕ) : Prop :=
  orderOf ((a : ZMod p)) = p - 1

/-- **Artin's conjecture on primitive roots.**  For every integer `a` which is neither `-1`
nor a perfect square, there are infinitely many primes `p` having `a` as a primitive root. -/
def ArtinConjecture : Prop :=
  ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}.Infinite

/-- A finite, decidable criterion for the order of an element of a monoid: `orderOf x = n`
as soon as `x ^ n = 1` and `x ^ (n / q) ≠ 1` for each prime divisor `q` of `n`. -/
theorem orderOf_eq_of_divisors {M : Type*} [Monoid M] (x : M) (n : ℕ) (hn : 0 < n)
    (h1 : x ^ n = 1) (h2 : ∀ q ∈ n.divisors, q.Prime → x ^ (n / q) ≠ 1) :
    orderOf x = n :=
  orderOf_eq_of_pow_and_pow_div_prime hn h1
    (fun q hq hd => h2 q (Nat.mem_divisors.mpr ⟨hd, hn.ne'⟩) hq)

/-- The primitive-root property is detected by a finite computation. -/
theorem isPrimitiveRootMod_of_divisors (a : ℤ) (p : ℕ) (hp : 0 < p - 1)
    (h1 : (a : ZMod p) ^ (p - 1) = 1)
    (h2 : ∀ q ∈ (p - 1).divisors, q.Prime → (a : ZMod p) ^ ((p - 1) / q) ≠ 1) :
    IsPrimitiveRootMod a p :=
  orderOf_eq_of_divisors _ _ hp h1 h2

/-- A perfect square is never a primitive root modulo an odd prime: this shows that the
hypothesis `¬ IsSquare a` in Artin's conjecture cannot be dropped. -/
theorem not_isPrimitiveRootMod_of_isSquare {a : ℤ} (ha : IsSquare a) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) : ¬ IsPrimitiveRootMod a p := by
  obtain ⟨b, rfl⟩ := ha
  intro h
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hodd
  have hp2 := hp.two_le
  have hp3 : 3 ≤ p := by omega
  have hpos : 0 < p - 1 := by omega
  have hx1 : ((b * b : ℤ) : ZMod p) ^ (p - 1) = 1 := by
    rw [← h]; exact pow_orderOf_eq_one _
  have hb0 : ((b : ℤ) : ZMod p) ≠ 0 := by
    intro hb
    rw [Int.cast_mul, hb, zero_mul, zero_pow hpos.ne'] at hx1
    exact zero_ne_one hx1
  have h2dvd : 2 ∣ p - 1 := by omega
  have hhalf : ((b * b : ℤ) : ZMod p) ^ ((p - 1) / 2) = 1 := by
    have : ((b * b : ℤ) : ZMod p) ^ ((p - 1) / 2)
        = ((b : ℤ) : ZMod p) ^ (2 * ((p - 1) / 2)) := by
      rw [Int.cast_mul, pow_mul]
      ring
    rw [this, Nat.mul_div_cancel' h2dvd]
    exact ZMod.pow_card_sub_one_eq_one hb0
  have hdvd : orderOf ((b * b : ℤ) : ZMod p) ∣ (p - 1) / 2 := orderOf_dvd_of_pow_eq_one hhalf
  rw [h] at hdvd
  have hhpos : 0 < (p - 1) / 2 := by omega
  have := Nat.le_of_dvd hhpos hdvd
  omega

/-- `-1` is never a primitive root modulo a prime `p ≥ 5`: this shows that the hypothesis
`a ≠ -1` in Artin's conjecture cannot be dropped. -/
theorem not_isPrimitiveRootMod_neg_one {p : ℕ} (hp : 5 ≤ p) :
    ¬ IsPrimitiveRootMod (-1) p := by
  intro h
  have hsq : ((-1 : ℤ) : ZMod p) ^ 2 = 1 := by
    push_cast
    ring
  have hdvd : orderOf (((-1 : ℤ) : ZMod p)) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rw [h] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

section BaseCases

private theorem cast_two (p : ℕ) : ((2 : ℤ) : ZMod p) = 2 := by push_cast; ring

theorem two_primitiveRoot_3 : IsPrimitiveRootMod 2 3 := by
  show orderOf ((2 : ℤ) : ZMod 3) = 2
  rw [cast_two]
  exact orderOf_eq_of_divisors _ _ (by norm_num) (by decide) (by decide)

theorem two_primitiveRoot_5 : IsPrimitiveRootMod 2 5 := by
  show orderOf ((2 : ℤ) : ZMod 5) = 4
  rw [cast_two]
  exact orderOf_eq_of_divisors _ _ (by norm_num) (by decide) (by decide)

theorem two_primitiveRoot_11 : IsPrimitiveRootMod 2 11 := by
  show orderOf ((2 : ℤ) : ZMod 11) = 10
  rw [cast_two]
  exact orderOf_eq_of_divisors _ _ (by norm_num) (by decide) (by decide)

theorem two_primitiveRoot_13 : IsPrimitiveRootMod 2 13 := by
  show orderOf ((2 : ℤ) : ZMod 13) = 12
  rw [cast_two]
  exact orderOf_eq_of_divisors _ _ (by norm_num) (by decide) (by decide)

theorem two_primitiveRoot_19 : IsPrimitiveRootMod 2 19 := by
  show orderOf ((2 : ℤ) : ZMod 19) = 18
  rw [cast_two]
  exact orderOf_eq_of_divisors _ _ (by norm_num) (by decide) (by decide)

theorem two_primitiveRoot_29 : IsPrimitiveRootMod 2 29 := by
  show orderOf ((2 : ℤ) : ZMod 29) = 28
  rw [cast_two]
  exact orderOf_eq_of_divisors _ _ (by norm_num) (by decide) (by decide)

theorem two_primitiveRoot_37 : IsPrimitiveRootMod 2 37 := by
  show orderOf ((2 : ℤ) : ZMod 37) = 36
  rw [cast_two]
  exact orderOf_eq_of_divisors _ _ (by norm_num) (by decide) (by decide)

theorem two_primitiveRoot_53 : IsPrimitiveRootMod 2 53 := by
  show orderOf ((2 : ℤ) : ZMod 53) = 52
  rw [cast_two]
  exact orderOf_eq_of_divisors _ _ (by norm_num) (by decide) (by decide)

theorem two_primitiveRoot_59 : IsPrimitiveRootMod 2 59 := by
  show orderOf ((2 : ℤ) : ZMod 59) = 58
  rw [cast_two]
  exact orderOf_eq_of_divisors _ _ (by norm_num) (by decide) (by decide)

theorem two_primitiveRoot_61 : IsPrimitiveRootMod 2 61 := by
  show orderOf ((2 : ℤ) : ZMod 61) = 60
  rw [cast_two]
  exact orderOf_eq_of_divisors _ _ (by norm_num) (by decide) (by decide)

theorem two_primitiveRoot_67 : IsPrimitiveRootMod 2 67 := by
  show orderOf ((2 : ℤ) : ZMod 67) = 66
  rw [cast_two]
  exact orderOf_eq_of_divisors _ _ (by norm_num) (by decide) (by decide)

theorem two_primitiveRoot_83 : IsPrimitiveRootMod 2 83 := by
  show orderOf ((2 : ℤ) : ZMod 83) = 82
  rw [cast_two]
  exact orderOf_eq_of_divisors _ _ (by norm_num) (by decide) (by decide)

end BaseCases

/-- **Artin's primitive root problem.**  The conjecture itself (`Frontier.ArtinConjecture`)
is open; what is proved here is:

* a Lean-checked *reduction* of the primitive-root condition to a finite, decidable
  computation over the divisors of `p - 1`;
* the resulting *base cases*: `2` is a primitive root modulo each of the twelve primes
  `3, 5, 11, 13, 19, 29, 37, 53, 59, 61, 67, 83` (so the set of primes for which Artin's
  conjecture asserts infinitude is at least non-empty for `a = 2`);
* the *necessity* of the two hypotheses on `a`: a perfect square is never a primitive root
  modulo an odd prime, and `-1` is never a primitive root modulo a prime `p ≥ 5`. -/
theorem artin_primitive_root :
    (∀ (a : ℤ) (p : ℕ), 0 < p - 1 → (a : ZMod p) ^ (p - 1) = 1 →
        (∀ q ∈ (p - 1).divisors, q.Prime → (a : ZMod p) ^ ((p - 1) / q) ≠ 1) →
        IsPrimitiveRootMod a p) ∧
    (∀ p ∈ ({3, 5, 11, 13, 19, 29, 37, 53, 59, 61, 67, 83} : Finset ℕ),
        p.Prime ∧ IsPrimitiveRootMod 2 p) ∧
    (∀ a : ℤ, IsSquare a → ∀ p : ℕ, p.Prime → Odd p → ¬ IsPrimitiveRootMod a p) ∧
    (∀ p : ℕ, p.Prime → 5 ≤ p → ¬ IsPrimitiveRootMod (-1) p) := by
  refine ⟨isPrimitiveRootMod_of_divisors, ?_, ?_, ?_⟩
  · intro p hp
    fin_cases hp
    exacts [⟨by norm_num, two_primitiveRoot_3⟩, ⟨by norm_num, two_primitiveRoot_5⟩,
      ⟨by norm_num, two_primitiveRoot_11⟩, ⟨by norm_num, two_primitiveRoot_13⟩,
      ⟨by norm_num, two_primitiveRoot_19⟩, ⟨by norm_num, two_primitiveRoot_29⟩,
      ⟨by norm_num, two_primitiveRoot_37⟩, ⟨by norm_num, two_primitiveRoot_53⟩,
      ⟨by norm_num, two_primitiveRoot_59⟩, ⟨by norm_num, two_primitiveRoot_61⟩,
      ⟨by norm_num, two_primitiveRoot_67⟩, ⟨by norm_num, two_primitiveRoot_83⟩]
  · intro a ha p hp hodd
    exact not_isPrimitiveRootMod_of_isSquare ha hp hodd
  · intro p _ hp5
    exact not_isPrimitiveRootMod_neg_one hp5

end Frontier

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

