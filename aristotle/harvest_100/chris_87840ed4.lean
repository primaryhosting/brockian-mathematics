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

/-
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Brockian.CarmichaelKorselt

/-- A Carmichael number: a composite `n > 1` which is a Fermat pseudoprime to every base
coprime to it. -/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ a : ℕ, Nat.Coprime a n → a ^ (n - 1) ≡ 1 [MOD n]

/-- The set of Carmichael numbers that are a product of three distinct primes. -/
def ThreePrimeCarmichaelSet : Set ℕ :=
  {n : ℕ | IsCarmichael n ∧ ∃ p q r : ℕ,
      p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧ n = p * q * r}

/-- Chernick's hypothesis: there are infinitely many `k > 0` for which `6k+1`, `12k+1` and
`18k+1` are all prime. (This is a consequence of the Dickson / Hardy–Littlewood
prime `k`-tuple conjecture and is not known unconditionally.) -/
def ChernickHypothesis : Prop :=
  {k : ℕ | 0 < k ∧ Nat.Prime (6 * k + 1) ∧ Nat.Prime (12 * k + 1) ∧ Nat.Prime (18 * k + 1)}.Infinite

/-- Fermat's little theorem in the form needed for Korselt's criterion. -/
theorem pow_modEq_one_of_sub_one_dvd {p m a : ℕ} (hp : p.Prime) (hdvd : (p - 1) ∣ m)
    (ha : Nat.Coprime a p) : a ^ m ≡ 1 [MOD p] := by
  obtain ⟨t, rfl⟩ := hdvd
  have hφ : Nat.totient p = p - 1 := Nat.totient_prime hp
  calc a ^ ((p - 1) * t) = (a ^ Nat.totient p) ^ t := by rw [hφ, pow_mul]
    _ ≡ 1 ^ t [MOD p] := Nat.ModEq.pow t (Nat.ModEq.pow_totient ha)
    _ = 1 := one_pow t

/-- Korselt's criterion (sufficiency) for a product of three distinct primes. -/
theorem isCarmichael_of_three_primes {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (h1 : (p - 1) ∣ (p * q * r - 1)) (h2 : (q - 1) ∣ (p * q * r - 1))
    (h3 : (r - 1) ∣ (p * q * r - 1)) : IsCarmichael (p * q * r) := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hr2 := hr.two_le
  have hcpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hcpr : Nat.Coprime p r := (Nat.coprime_primes hp hr).mpr hpr
  have hcqr : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hqr
  have hpq2 : 2 * 2 ≤ p * q := Nat.mul_le_mul hp2 hq2
  have hlt : 1 < p * q * r := by
    have := Nat.mul_le_mul hpq2 hr2
    omega
  refine ⟨hlt, ?_, ?_⟩
  · exact Nat.not_prime_mul (by omega) (by omega)
  · intro a ha
    have hap : Nat.Coprime a p := Nat.Coprime.coprime_dvd_right ⟨q * r, by ring⟩ ha
    have haq : Nat.Coprime a q := Nat.Coprime.coprime_dvd_right ⟨p * r, by ring⟩ ha
    have har : Nat.Coprime a r := Nat.Coprime.coprime_dvd_right ⟨p * q, by ring⟩ ha
    have e1 : a ^ (p * q * r - 1) ≡ 1 [MOD p] := pow_modEq_one_of_sub_one_dvd hp h1 hap
    have e2 : a ^ (p * q * r - 1) ≡ 1 [MOD q] := pow_modEq_one_of_sub_one_dvd hq h2 haq
    have e3 : a ^ (p * q * r - 1) ≡ 1 [MOD r] := pow_modEq_one_of_sub_one_dvd hr h3 har
    have e12 : a ^ (p * q * r - 1) ≡ 1 [MOD p * q] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcpq).mp ⟨e1, e2⟩
    exact (Nat.modEq_and_modEq_iff_modEq_mul (Nat.Coprime.mul_left hcpr hcqr)).mp ⟨e12, e3⟩

/-- The Chernick construction: if `6k+1`, `12k+1`, `18k+1` are all prime (`k > 0`), then their
product is a Carmichael number with three distinct prime factors. -/
theorem chernick_mem_threePrimeCarmichaelSet {k : ℕ} (hk : 0 < k)
    (hp : Nat.Prime (6 * k + 1)) (hq : Nat.Prime (12 * k + 1)) (hr : Nat.Prime (18 * k + 1)) :
    (6 * k + 1) * (12 * k + 1) * (18 * k + 1) ∈ ThreePrimeCarmichaelSet := by
  have hprod : (6 * k + 1) * (12 * k + 1) * (18 * k + 1)
      = 36 * k * (36 * k ^ 2 + 11 * k + 1) + 1 := by ring
  have hsub : (6 * k + 1) * (12 * k + 1) * (18 * k + 1) - 1
      = 36 * k * (36 * k ^ 2 + 11 * k + 1) := by omega
  have hcar : IsCarmichael ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)) := by
    refine isCarmichael_of_three_primes hp hq hr (by omega) (by omega) (by omega) ?_ ?_ ?_ <;>
      rw [hsub]
    · exact ⟨6 * (36 * k ^ 2 + 11 * k + 1), by simp only [Nat.add_sub_cancel]; ring⟩
    · exact ⟨3 * (36 * k ^ 2 + 11 * k + 1), by simp only [Nat.add_sub_cancel]; ring⟩
    · exact ⟨2 * (36 * k ^ 2 + 11 * k + 1), by simp only [Nat.add_sub_cancel]; ring⟩
  exact ⟨hcar, _, _, _, hp, hq, hr, by omega, by omega, rfl⟩

/-- Unconditionally, `561 = 3 * 11 * 17` is a Carmichael number with three prime factors. -/
theorem mem_threePrimeCarmichaelSet_561 : (561 : ℕ) ∈ ThreePrimeCarmichaelSet := by
  have h : (561 : ℕ) = 3 * 11 * 17 := by norm_num
  rw [h]
  exact ⟨isCarmichael_of_three_primes (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    3, 11, 17, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩

/-- The hypothesis is satisfiable: `k = 1` gives the Carmichael number `1729 = 7 * 13 * 19`. -/
theorem mem_threePrimeCarmichaelSet_1729 : (1729 : ℕ) ∈ ThreePrimeCarmichaelSet := by
  have h : (1729 : ℕ) = (6 * 1 + 1) * (12 * 1 + 1) * (18 * 1 + 1) := by norm_num
  rw [h]
  exact chernick_mem_threePrimeCarmichaelSet Nat.one_pos (by norm_num) (by norm_num) (by norm_num)

/-- **Three Prime Carmichael Infinitude** (conditional on Chernick's hypothesis).

If there are infinitely many `k > 0` such that `6k+1`, `12k+1` and `18k+1` are all prime, then
there are infinitely many Carmichael numbers that are products of exactly three distinct primes.
The infinitude of three-factor Carmichael numbers is not known unconditionally; this is a
Lean-checked reduction of it to a prime-tuple hypothesis. -/
theorem ThreePrimeCarmichaelInfinitude (h : ChernickHypothesis) :
    ThreePrimeCarmichaelSet.Infinite := by
  have hmono : StrictMono (fun k : ℕ => (6 * k + 1) * (12 * k + 1) * (18 * k + 1)) := by
    intro a b hab
    simp only
    gcongr
  refine Set.Infinite.mono ?_ (h.image hmono.injective.injOn)
  rintro n ⟨k, ⟨hk, hp, hq, hr⟩, rfl⟩
  exact chernick_mem_threePrimeCarmichaelSet hk hp hq hr

end Brockian.CarmichaelKorselt

