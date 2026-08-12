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
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ErdosStraus

/-- `ErdosStrausRepr n` says that `4/n` is a sum of three positive unit fractions. -/
def ErdosStrausRepr (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-- If `4/m` has a representation and `k ≥ 1`, then so does `4/(m*k)`. -/
theorem ErdosStrausRepr.mul {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (h : ErdosStrausRepr m) : ErdosStrausRepr (m * k) := by
  obtain ⟨x, y, z, hx, hy, hz, hrepr⟩ := h
  refine ⟨k * x, k * y, k * z, by positivity, by positivity, by positivity, ?_⟩
  have hxq : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hyq : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hzq : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hmq : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have h2 : (4 : ℚ) / ((m : ℚ) * k) = ((4 : ℚ) / m) / k := by
    field_simp
  push_cast
  rw [h2, hrepr]
  field_simp

/-- If `m ∣ n`, `m ≥ 1`, `n ≥ 1` and `4/m` is representable, then so is `4/n`. -/
theorem ErdosStrausRepr.of_dvd {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hdvd : m ∣ n)
    (h : ErdosStrausRepr m) : ErdosStrausRepr n := by
  obtain ⟨k, rfl⟩ := hdvd
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hn
    · exact hk
  exact h.mul hm hk

/-- Even case: `4/(2m) = 1/m + 1/(2m) + 1/(2m)`. -/
theorem repr_of_even {n : ℕ} (hn : 0 < n) (h : n % 2 = 0) : ErdosStrausRepr n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  have hm : 0 < m := by omega
  refine ⟨m, 2 * m, 2 * m, hm, by omega, by omega, ?_⟩
  have hmq : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  push_cast
  field_simp
  ring

/-- Case `n ≡ 3 [MOD 4]`: `4/n = 1/(k+1) + 1/(2n(k+1)) + 1/(2n(k+1))` with `n = 4k+3`. -/
theorem repr_of_mod_four_eq_three {n : ℕ} (h : n % 4 = 3) : ErdosStrausRepr n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  refine ⟨k + 1, 2 * (4 * k + 3) * (k + 1), 2 * (4 * k + 3) * (k + 1),
    by omega, by positivity, by positivity, ?_⟩
  have h1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have h2 : (4 * (k : ℚ) + 3) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Case `n ≡ 2 [MOD 3]`: `4/n = 1/n + 1/(k+1) + 1/(n(k+1))` with `n = 3k+2`. -/
theorem repr_of_mod_three_eq_two {n : ℕ} (h : n % 3 = 2) : ErdosStrausRepr n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
  refine ⟨3 * k + 2, k + 1, (3 * k + 2) * (k + 1),
    by omega, by omega, by positivity, ?_⟩
  have h1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have h2 : (3 * (k : ℚ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Every prime `p` with `p % 12 ≠ 1` admits a representation. -/
theorem repr_of_prime_of_mod_twelve_ne_one {p : ℕ} (hp : p.Prime) (h : p % 12 ≠ 1) :
    ErdosStrausRepr p := by
  have hp2 : 2 ≤ p := hp.two_le
  by_cases he : p % 2 = 0
  · exact repr_of_even (by omega) he
  by_cases h4 : p % 4 = 3
  · exact repr_of_mod_four_eq_three h4
  by_cases h3 : p % 3 = 2
  · exact repr_of_mod_three_eq_two h3
  -- remaining: p % 4 = 1 and p % 3 ∈ {0, 1}; p % 3 = 0 forces p = 3, contradiction
  exfalso
  have h30 : p % 3 = 0 ∨ p % 3 = 1 := by omega
  rcases h30 with h30 | h31
  · have : (3 : ℕ) ∣ p := by omega
    have := (Nat.Prime.eq_one_or_self_of_dvd hp 3 this)
    omega
  · omega

/-- **Erdős–Straus reduction.** If every prime `p ≡ 1 [MOD 12]` admits a representation
of `4/p` as a sum of three unit fractions, then every `n ≥ 2` does. In particular the
Erdős–Straus conjecture is equivalent to its restriction to primes congruent to `1` mod `12`. -/
theorem ErdosStrausConjecture
    (h : ∀ p : ℕ, p.Prime → p % 12 = 1 → ErdosStrausRepr p) :
    ∀ n : ℕ, 2 ≤ n → ErdosStrausRepr n := by
  intro n hn
  have hn1 : n ≠ 1 := by omega
  have hp : (n.minFac).Prime := Nat.minFac_prime hn1
  have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hrep : ErdosStrausRepr n.minFac := by
    by_cases hm : n.minFac % 12 = 1
    · exact h _ hp hm
    · exact repr_of_prime_of_mod_twelve_ne_one hp hm
  exact hrep.of_dvd hp.pos (by omega) hdvd

/-- Unconditional consequence: any `n ≥ 2` having a prime factor not congruent to `1` mod `12`
admits a representation. -/
theorem repr_of_exists_prime_factor {n : ℕ} (hn : 2 ≤ n)
    (hex : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 12 ≠ 1) : ErdosStrausRepr n := by
  obtain ⟨p, hp, hdvd, hmod⟩ := hex
  exact (repr_of_prime_of_mod_twelve_ne_one hp hmod).of_dvd hp.pos (by omega) hdvd

/-! ### Explicit representations for the small primes `≡ 1 [MOD 12]` -/

theorem repr_thirteen : ErdosStrausRepr 13 :=
  ⟨4, 18, 468, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem repr_thirtyseven : ErdosStrausRepr 37 :=
  ⟨10, 124, 22940, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem repr_sixtyone : ErdosStrausRepr 61 :=
  ⟨16, 326, 159088, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem repr_seventythree : ErdosStrausRepr 73 :=
  ⟨20, 210, 30660, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem repr_ninetyseven : ErdosStrausRepr 97 :=
  ⟨25, 810, 392850, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The primes `p ≤ 100` with `p ≡ 1 [MOD 12]`. -/
theorem prime_mod_twelve_eq_one_le_hundred {p : ℕ} (hp : p.Prime) (hm : p % 12 = 1)
    (hle : p ≤ 100) : p = 13 ∨ p = 37 ∨ p = 61 ∨ p = 73 ∨ p = 97 := by
  have hp2 := hp.two_le
  interval_cases p <;> first | omega | norm_num at hp

/-- Unconditionally, the Erdős–Straus conjecture holds for every `2 ≤ n ≤ 100`. -/
theorem repr_of_le_hundred {n : ℕ} (hn : 2 ≤ n) (hn' : n ≤ 100) : ErdosStrausRepr n := by
  have hn1 : n ≠ 1 := by omega
  have hp : (n.minFac).Prime := Nat.minFac_prime hn1
  have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hle : n.minFac ≤ 100 := le_trans (Nat.minFac_le (by omega)) hn'
  have hrep : ErdosStrausRepr n.minFac := by
    by_cases hm : n.minFac % 12 = 1
    · rcases prime_mod_twelve_eq_one_le_hundred hp hm hle with h | h | h | h | h <;> rw [h]
      · exact repr_thirteen
      · exact repr_thirtyseven
      · exact repr_sixtyone
      · exact repr_seventythree
      · exact repr_ninetyseven
    · exact repr_of_prime_of_mod_twelve_ne_one hp hm
  exact hrep.of_dvd hp.pos (by omega) hdvd

end Brockian.ErdosStraus

