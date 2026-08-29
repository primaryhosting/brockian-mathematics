/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number, spelled out from first principles:
`p` is at least `2` and has no divisor `d` with `2 ≤ d < p`.
(This is proved equivalent to Mathlib's `Nat.Prime` in
`RequestProject/GoldbachWheelK2_1153Mathlib.lean`.) -/
def IsPrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d < p → 2 ≤ d → ¬ d ∣ p

instance (p : Nat) : Decidable (IsPrimeNat p) := by
  unfold IsPrimeNat; infer_instance

/-- A prime other than `2` is odd. -/
theorem IsPrimeNat.odd_of_ne_two {p : Nat} (hp : IsPrimeNat p) (h : p ≠ 2) : p % 2 = 1 := by
  obtain ⟨h2, hd⟩ := hp
  have := hd 2 (by omega) (by omega)
  omega

set_option maxRecDepth 8000 in
/-- `1151` is prime. -/
theorem isPrimeNat_1151 : IsPrimeNat 1151 := by decide

/-- `2` is prime. -/
theorem isPrimeNat_two : IsPrimeNat 2 := by decide

/-- **Goldbach wheel with `K = 2` at the modulus `1153`.**

The odd number `1153` is a sum of two primes, namely `1153 = 2 + 1151`, and this
decomposition is unique: any ordered pair of primes summing to `1153` is `(2, 1151)`
or `(1151, 2)`.  Thus the wheel of admissible prime pairs for `1153` collapses to the
single unordered pair `{2, 1151}`. -/
theorem GoldbachWheelK2_1153 :
    (∃ p q : Nat, IsPrimeNat p ∧ IsPrimeNat q ∧ p + q = 1153) ∧
    (∀ p q : Nat, IsPrimeNat p → IsPrimeNat q → p + q = 1153 →
      (p = 2 ∧ q = 1151) ∨ (p = 1151 ∧ q = 2)) := by
  refine ⟨⟨2, 1151, isPrimeNat_two, isPrimeNat_1151, rfl⟩, ?_⟩
  intro p q hp hq hpq
  by_cases hp2 : p = 2
  · exact Or.inl ⟨hp2, by omega⟩
  · by_cases hq2 : q = 2
    · exact Or.inr ⟨by omega, hq2⟩
    · exact absurd hpq (by have := hp.odd_of_ne_two hp2; have := hq.odd_of_ne_two hq2; omega)

end Brockian

import Mathlib
import RequestProject.GoldbachWheelK2_1153

/-!
# Goldbach Wheel K 2 1153 — Mathlib interface

The target theorem `Brockian.GoldbachWheelK2_1153` is stated with the self-contained
primality predicate `Brockian.IsPrimeNat` (its file must be import-free so that the
required header comment can be the very first thing in the file).  Here we check that
this predicate agrees with Mathlib's `Nat.Prime`, and restate the result accordingly.
-/

namespace Brockian

/-- `IsPrimeNat` agrees with Mathlib's `Nat.Prime`. -/
theorem isPrimeNat_iff_prime {p : ℕ} : IsPrimeNat p ↔ Nat.Prime p := by
  constructor
  · rintro ⟨h2, hd⟩
    refine Nat.prime_def.mpr ⟨h2, fun d hdvd => ?_⟩
    rcases Nat.lt_or_ge d p with hlt | hge
    · rcases Nat.lt_or_ge d 2 with hd2 | hd2
      · interval_cases d
        · simp at hdvd; omega
        · exact Or.inl rfl
      · exact absurd hdvd (hd d hlt hd2)
    · exact Or.inr (Nat.le_antisymm (Nat.le_of_dvd (by omega) hdvd) hge)
  · intro hp
    exact ⟨hp.two_le, fun d hlt hd2 hdvd => by
      rcases (Nat.Prime.eq_one_or_self_of_dvd hp d hdvd) with h | h <;> omega⟩

/-- The Goldbach wheel statement for `1153`, phrased with Mathlib's `Nat.Prime`. -/
theorem goldbachWheelK2_1153_prime :
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 1153) ∧
    (∀ p q : ℕ, p.Prime → q.Prime → p + q = 1153 →
      ({p, q} : Finset ℕ) = ({2, 1151} : Finset ℕ)) := by
  obtain ⟨⟨p, q, hp, hq, hpq⟩, huniq⟩ := GoldbachWheelK2_1153
  refine ⟨⟨p, q, isPrimeNat_iff_prime.mp hp, isPrimeNat_iff_prime.mp hq, hpq⟩, ?_⟩
  intro a b ha hb hab
  rcases huniq a b (isPrimeNat_iff_prime.mpr ha) (isPrimeNat_iff_prime.mpr hb) hab with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
  · rfl
  · exact Finset.pair_comm 1151 2

end Brockian

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

