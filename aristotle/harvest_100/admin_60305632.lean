import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Brockian

/-- Trial division helper: `noFactorFrom f d n` is `true` when none of
`d, d+1, …` (up to `f` steps, stopping as soon as the divisor squared exceeds `n`)
divides `n`. -/
def noFactorFrom : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | (f + 1), d, n =>
      if n < d * d then true else if n % d == 0 then false else noFactorFrom f (d + 1) n

/-- Kernel-friendly primality test by trial division. -/
def primeB (n : ℕ) : Bool := 2 ≤ n && noFactorFrom n 2 n

theorem noFactorFrom_spec : ∀ (f d n : ℕ), noFactorFrom f d n = true →
    ∀ k, d ≤ k → k < d + f → k * k ≤ n → ¬ k ∣ n := by
  intro f
  induction f with
  | zero => intro d n _ k hdk hlt _; omega
  | succ f ih =>
    intro d n h k hdk hlt hkk hdvd
    rw [noFactorFrom] at h
    by_cases h1 : n < d * d
    · have : d * d ≤ k * k := Nat.mul_le_mul hdk hdk
      omega
    · rw [if_neg h1] at h
      by_cases h2 : n % d == 0
      · rw [if_pos h2] at h; exact absurd h (by simp)
      · rw [if_neg h2] at h
        rcases eq_or_lt_of_le hdk with rfl | hlt2
        · simp only [beq_iff_eq] at h2
          exact h2 (Nat.dvd_iff_mod_eq_zero.mp hdvd)
        · exact ih (d + 1) n h k hlt2 (by omega) hkk hdvd

/-- Soundness of the Boolean primality test. -/
theorem prime_of_primeB {n : ℕ} (h : primeB n = true) : Nat.Prime n := by
  rw [primeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hnf⟩ := h
  by_contra hp
  have hpos : 0 < n := by omega
  have hle := Nat.minFac_sq_le_self hpos hp
  have hdvd := Nat.minFac_dvd n
  have h2m : 2 ≤ n.minFac := (Nat.minFac_prime (by omega)).two_le
  have hmn : n.minFac ≤ n := Nat.minFac_le hpos
  exact noFactorFrom_spec n 2 n hnf n.minFac h2m (by omega)
    (by nlinarith [sq_nonneg n.minFac, hle]) hdvd

/-- A number whose residue mod `6` is `1` or `5` is coprime to the `K = 2` wheel
modulus `6 = 2 * 3`. -/
theorem coprime_six_of_mod {p : ℕ} (h : p % 6 = 1 ∨ p % 6 = 5) : Nat.Coprime p 6 := by
  have : Nat.gcd 6 p = Nat.gcd (p % 6) 6 := Nat.gcd_rec 6 p
  rcases h with h | h <;>
    · rw [h] at this
      simp [Nat.Coprime, Nat.gcd_comm p 6, this]

/-- The verified wheel table: for every `m` with `5 ≤ m ≤ 525` the even number `2 * m`
splits as `p + (2 * m - p)` with both summands prime and coprime to the wheel modulus `6`,
where `p` is drawn from the fixed list of wheel primes below. -/
theorem wheelTable : ∀ m ∈ Finset.Icc 5 525,
    ∃ p ∈ ([5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73] : List ℕ),
      primeB p = true ∧ primeB (2 * m - p) = true ∧ p + (2 * m - p) = 2 * m ∧
        (p % 6 = 1 ∨ p % 6 = 5) ∧ ((2 * m - p) % 6 = 1 ∨ (2 * m - p) % 6 = 5) := by decide

/--
**Goldbach Wheel, K = 2, bound 1051.**

Two statements about the even numbers up to `1051`:

* every even `n` with `4 ≤ n ≤ 1051` is a sum of two primes;
* (wheel refinement for the `K = 2` wheel, i.e. modulus `2 * 3 = 6`) every even `n`
  with `10 ≤ n ≤ 1051` is a sum of two primes *both coprime to `6`*, i.e. both lying
  on the wheel of the first two primes. (The bound `10` is sharp: `4 = 2 + 2`,
  `6 = 3 + 3` and `8 = 3 + 5` all need a prime dividing `6`.)
-/
theorem GoldbachWheelK2_1051 :
    (∀ n : ℕ, 4 ≤ n → n ≤ 1051 → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n) ∧
    (∀ n : ℕ, 10 ≤ n → n ≤ 1051 → Even n →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n ∧ Nat.Coprime p 6 ∧ Nat.Coprime q 6) := by
  have wheel : ∀ n : ℕ, 10 ≤ n → n ≤ 1051 → Even n →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n ∧ Nat.Coprime p 6 ∧ Nat.Coprime q 6 := by
    intro n h10 h1051 hev
    obtain ⟨m, rfl⟩ := hev
    have hm : m ∈ Finset.Icc 5 525 := by simp only [Finset.mem_Icc]; omega
    obtain ⟨p, -, hp, hq, hsum, hpm, hqm⟩ := wheelTable m hm
    exact ⟨p, 2 * m - p, prime_of_primeB hp, prime_of_primeB hq, by omega,
      coprime_six_of_mod hpm, coprime_six_of_mod hqm⟩
  refine ⟨?_, wheel⟩
  intro n h4 h1051 hev
  by_cases h10 : 10 ≤ n
  · obtain ⟨p, q, hp, hq, hsum, -, -⟩ := wheel n h10 h1051 hev
    exact ⟨p, q, hp, hq, hsum⟩
  · obtain ⟨m, rfl⟩ := hev
    have hlo : 2 ≤ m := by omega
    have hhi : m ≤ 4 := by omega
    interval_cases m
    · exact ⟨2, 2, by norm_num, by norm_num, rfl⟩
    · exact ⟨3, 3, by norm_num, by norm_num, rfl⟩
    · exact ⟨3, 5, by norm_num, by norm_num, rfl⟩

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

