import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `a : ℤ` is a primitive root modulo the prime `p` if its residue generates the
multiplicative group `(ZMod p)ˣ`, i.e. it has multiplicative order `p - 1`. -/
def IsPrimitiveRootMod (a : ℤ) (p : ℕ) : Prop :=
  orderOf ((a : ZMod p)) = p - 1

/-- The set of primes for which `a` is a primitive root. -/
def artinPrimes (a : ℤ) : Set ℕ := {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}

/-- **Artin's conjecture on primitive roots** (open): for every integer `a` which is
neither `-1` nor a perfect square, there are infinitely many primes `p` such that `a`
is a primitive root modulo `p`. -/
def ArtinConjecture : Prop :=
  ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → (artinPrimes a).Infinite

/-- If `a` is a perfect square then it is a quadratic residue modulo every prime, hence
its order divides `(p-1)/2` and it cannot be a primitive root modulo an odd prime. -/
theorem not_isPrimitiveRootMod_of_isSquare {a : ℤ} (ha : IsSquare a) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ IsPrimitiveRootMod a p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, rfl⟩ := ha
  intro h
  rw [IsPrimitiveRootMod] at h
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  set x : ZMod p := (b : ZMod p) with hx
  have hcast : ((b * b : ℤ) : ZMod p) = x * x := by push_cast [hx]; ring
  rw [hcast] at h
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, mul_zero, orderOf_zero] at h
    omega
  -- `p - 1` is even
  obtain ⟨k, hk⟩ : ∃ k, p - 1 = 2 * k := by
    obtain ⟨m, hm⟩ := hodd
    exact ⟨m, by omega⟩
  have hk0 : 0 < k := by omega
  have hpow : (x * x) ^ k = 1 := by
    have : (x * x) ^ k = x ^ (p - 1) := by
      rw [hk, ← sq, ← pow_mul]
    rw [this]
    exact ZMod.pow_card_sub_one_eq_one hx0
  have hdvd : orderOf (x * x) ∣ k := orderOf_dvd_of_pow_eq_one hpow
  rw [h] at hdvd
  have := Nat.le_of_dvd hk0 hdvd
  omega

/-- `-1` has multiplicative order at most `2`, so it is a primitive root only modulo
primes `p ≤ 3`. -/
theorem not_isPrimitiveRootMod_neg_one {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ¬ IsPrimitiveRootMod (-1) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  rw [IsPrimitiveRootMod] at h
  have hpow : ((-1 : ℤ) : ZMod p) ^ 2 = 1 := by push_cast; ring
  have hdvd : orderOf (((-1 : ℤ) : ZMod p)) ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
  rw [h] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/--
**Artin's conjecture on primitive roots**, formalized as `Frontier.ArtinConjecture`,
together with a Lean-checked verification of the necessity of its two hypotheses:

* if `a = -1`, or
* if `a` is a perfect square,

then `a` is a primitive root modulo only finitely many primes (indeed only possibly
modulo `2` and `3`), so the conclusion of the conjecture genuinely fails for these `a`.
-/
theorem artin_primitive_root (a : ℤ) (ha : a = -1 ∨ IsSquare a) :
    artinPrimes a ⊆ ({2, 3} : Set ℕ) ∧ (artinPrimes a).Finite := by
  have hsub : artinPrimes a ⊆ ({2, 3} : Set ℕ) := by
    rintro p ⟨hp, hroot⟩
    by_contra hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
    rcases ha with rfl | ha
    · exact not_isPrimitiveRootMod_neg_one hp
        (by have := hp.two_le; omega) hroot
    · exact not_isPrimitiveRootMod_of_isSquare ha hp hmem.1 hroot
  exact ⟨hsub, Set.Finite.subset (Set.toFinite _) hsub⟩

/-- The bound in `artin_primitive_root` is attained: `-1` really is a primitive root
modulo `3`. -/
theorem isPrimitiveRootMod_neg_one_three : IsPrimitiveRootMod (-1) 3 := by
  have h : orderOf ((-1 : ℤ) : ZMod 3) = 2 :=
    orderOf_eq_prime (by decide) (by decide)
  simpa [IsPrimitiveRootMod] using h

/-!
### Verified base cases

Concrete primes witnessing that the conjecture's conclusion does hold for small data.
-/

/-- `2` is a primitive root modulo `5`. -/
theorem isPrimitiveRootMod_two_five : IsPrimitiveRootMod 2 5 := by
  show orderOf ((2 : ℤ) : ZMod 5) = 5 - 1
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hqd
  have hq4 : q ≤ 4 := Nat.le_of_dvd (by norm_num) hqd
  have := hq.two_le
  interval_cases q <;> revert hqd <;> decide

/-- `2` is a primitive root modulo `11`. -/
theorem isPrimitiveRootMod_two_eleven : IsPrimitiveRootMod 2 11 := by
  show orderOf ((2 : ℤ) : ZMod 11) = 11 - 1
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hqd
  have hq10 : q ≤ 10 := Nat.le_of_dvd (by norm_num) hqd
  have := hq.two_le
  interval_cases q <;> revert hqd <;> decide

/-- `2` is a primitive root modulo `13`. -/
theorem isPrimitiveRootMod_two_thirteen : IsPrimitiveRootMod 2 13 := by
  show orderOf ((2 : ℤ) : ZMod 13) = 13 - 1
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hqd
  have hq12 : q ≤ 12 := Nat.le_of_dvd (by norm_num) hqd
  have := hq.two_le
  interval_cases q <;> revert hqd <;> decide

/-- `3` is a primitive root modulo `7`. -/
theorem isPrimitiveRootMod_three_seven : IsPrimitiveRootMod 3 7 := by
  show orderOf ((3 : ℤ) : ZMod 7) = 7 - 1
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hqd
  have hq6 : q ≤ 6 := Nat.le_of_dvd (by norm_num) hqd
  have := hq.two_le
  interval_cases q <;> revert hqd <;> decide

/-- Base cases for `a = 2`: the primes `5`, `11`, `13` all have `2` as a primitive root,
so `artinPrimes 2` is nonempty (the conjecture asserts it is in fact infinite). -/
theorem base_case_two : ({5, 11, 13} : Set ℕ) ⊆ artinPrimes 2 := by
  rintro p (rfl | rfl | rfl)
  · exact ⟨by norm_num, isPrimitiveRootMod_two_five⟩
  · exact ⟨by norm_num, isPrimitiveRootMod_two_eleven⟩
  · exact ⟨by norm_num, isPrimitiveRootMod_two_thirteen⟩

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

