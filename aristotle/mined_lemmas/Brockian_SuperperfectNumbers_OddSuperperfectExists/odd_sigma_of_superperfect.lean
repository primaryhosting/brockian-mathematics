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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Superperfect Exists

Category: Brockian Conjecture

Target: `Brockian.SuperperfectNumbers.OddSuperperfectExists`

A natural number `n` is *superperfect* when `σ (σ n) = 2 * n`, where `σ = σ₁` is the
sum-of-divisors function.  The even superperfect numbers are exactly the numbers `2 ^ k`
with `2 ^ (k + 1) - 1` prime; whether an **odd** superperfect number exists is an open
problem.  Accordingly this file does not claim the (open) existence statement.  Instead it
proves unconditional structural facts about a hypothetical odd superperfect number and
packages them as a Lean-checked *conditional reduction*:

* `odd_sigma_of_superperfect`: for every superperfect `n > 0`, `σ n` is odd;
* `isSquare_of_odd_superperfect`: every odd superperfect number is a perfect square
  (Suryanarayana);
* `not_superperfect_of_odd_lt`: there is no odd superperfect number below `4096`;
* `OddSuperperfectExists`: an odd superperfect number exists **iff** there is an odd
  superperfect perfect square that is at least `4096`.
-/

namespace Brockian.SuperperfectNumbers

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- `n` is *superperfect* when `σ (σ n) = 2 * n`, where `σ` is the sum-of-divisors
function. -/

theorem odd_sigma_of_superperfect {n : ℕ} (hn : 0 < n) (hsp : Superperfect n) :
    Odd (σ 1 n) := by
  rw [Superperfect] at hsp
  set m := σ 1 n with hm
  rw [Nat.odd_iff, ← Nat.not_even_iff]
  intro hev
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hsp
    simp [ArithmeticFunction.map_zero] at hsp
    omega
  set a := m.factorization 2 with hadef
  set u := m / 2 ^ a with hudef
  have hmu : 2 ^ a * u = m := Nat.ordProj_mul_ordCompl_eq_self m 2
  have hu0 : u ≠ 0 := by
    intro h; rw [h, Nat.mul_zero] at hmu; exact hm0 hmu.symm
  have ha1 : 1 ≤ a := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hm0 hev.two_dvd
  have hunotdvd : ¬ (2 ∣ u) := Nat.not_dvd_ordCompl Nat.prime_two hm0
  have hcop : Nat.Coprime (2 ^ a) u :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hunotdvd)
  have hmul : σ 1 m = σ 1 (2 ^ a) * σ 1 u := by
    rw [← hmu]; exact isMultiplicative_sigma.map_mul_of_coprime hcop
  set D := σ 1 (2 ^ a) with hDdef
  have hD : D + 1 = 2 ^ (a + 1) := sigma_two_pow_succ a
  have hD3 : 3 ≤ D := by
    have h4 : (4 : ℕ) ≤ 2 ^ (a + 1) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hDodd : ¬ (2 ∣ D) := by
    have h2 : 2 ∣ 2 ^ (a + 1) := dvd_pow_self 2 (by omega)
    omega
  have h2n : 2 * n = D * σ 1 u := by rw [← hmul, hsp]
  have hDn : D ∣ n :=
    Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hDodd)) ⟨σ 1 u, h2n⟩
  obtain ⟨k, hk⟩ := hDn
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h] at hk; omega
    · exact h
  have hsu : σ 1 u = 2 * k := by
    have h : D * (2 * k) = D * σ 1 u := by rw [← h2n, hk]; ring
    exact (Nat.eq_of_mul_eq_mul_left (by omega) h).symm
  have hu1 : 1 < u := by
    rcases Nat.lt_or_ge u 2 with h | h
    · interval_cases u
      · omega
      · simp at hsu; omega
    · omega
  have hsu_ge : u + 1 ≤ σ 1 u := by
    have := add_le_sigma_of_dvd (n := u) (a := 1) (b := u) (by omega) (one_dvd u) dvd_rfl (by omega)
    omega
  have hkn : k ∣ n := ⟨D, by rw [hk]; ring⟩
  have hkne : n ≠ k := by nlinarith [hk]
  have hbig : n + k ≤ m := by
    have := add_le_sigma_of_dvd (n := n) (a := n) (b := k) hn dvd_rfl hkn hkne
    omega
  have hD2 : D + 1 = 2 ^ a * 2 := by rw [hD]; ring
  have e1 : n + k = 2 ^ a * σ 1 u := by
    rw [hk, hsu]
    calc D * k + k = (D + 1) * k := by ring
      _ = 2 ^ a * 2 * k := by rw [hD2]
      _ = 2 ^ a * (2 * k) := by ring
  have e2 : 2 ^ a * (u + 1) ≤ 2 ^ a * σ 1 u := Nat.mul_le_mul_left _ hsu_ge
  have e3 : 2 ^ a * (u + 1) = m + 2 ^ a := by rw [← hmu]; ring
  have hpos : 0 < 2 ^ a := Nat.two_pow_pos a
  omega

/-- **Suryanarayana's theorem.**  Every odd superperfect number is a perfect square. -/
