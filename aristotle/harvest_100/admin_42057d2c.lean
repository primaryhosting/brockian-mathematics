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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
A natural number `n` is *quasiperfect* if `σ n = 2 * n + 1`, i.e. the sum of the proper
divisors of `n` (including `1`) equals `n + 1`.  No quasiperfect number is known, and their
existence is an open problem.

This file proves the classical structural constraints (Cattaneo, 1951): a quasiperfect number
must be an odd perfect square, and it cannot be a prime power.  The main theorem
`QuasiperfectExists` is the resulting *reduction*: a quasiperfect number exists if and only if
there is an odd `k > 1`, not a prime power, whose square is quasiperfect.
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if it is positive and the sum of all of its
divisors equals `2 * n + 1`. -/
def Quasiperfect (n : ℕ) : Prop :=
  0 < n ∧ ∑ d ∈ n.divisors, d = 2 * n + 1

/-- The divisor-sum function is multiplicative. -/
theorem sum_divisors_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    ∑ d ∈ (a * b).divisors, d = (∑ d ∈ a.divisors, d) * (∑ d ∈ b.divisors, d) := by
  have := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime h
  simpa [ArithmeticFunction.sigma_one_apply] using this

/-- The sum of divisors of a power of two. -/
theorem sum_divisors_two_pow (a : ℕ) : ∑ d ∈ (2 ^ a).divisors, d = 2 ^ (a + 1) - 1 := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  simp [Nat.geomSum_eq]

/-- An odd number whose sum of divisors is odd is a perfect square. -/
theorem isSquare_of_odd_sigma {n : ℕ} (hn : n ≠ 0) (hodd : Odd n)
    (h : Odd (∑ d ∈ n.divisors, d)) : IsSquare n := by
  have hcard : (∑ d ∈ n.divisors, d) % 2 = n.divisors.card % 2 := by
    rw [Finset.sum_nat_mod]
    have hd1 : ∀ d ∈ n.divisors, d % 2 = 1 := fun d hd =>
      Nat.odd_iff.mp (hodd.of_dvd_nat (Nat.dvd_of_mem_divisors hd))
    rw [Finset.sum_congr rfl hd1]
    simp
  have h2 : Odd n.divisors.card := by rw [Nat.odd_iff] at *; omega
  rw [Nat.card_divisors hn] at h2
  have hall : ∀ p ∈ n.primeFactors, Even (n.factorization p) := by
    intro p hp
    have hnd : ¬ (2 ∣ ∏ x ∈ n.primeFactors, (n.factorization x + 1)) := by
      rw [Nat.odd_iff] at h2; omega
    have h3 := (Nat.prime_two.prime.dvd_finset_prod_iff _).not.mp hnd
    push_neg at h3
    have h4 := h3 p hp
    rcases Nat.even_or_odd (n.factorization p) with he | ho
    · exact he
    · exact absurd (by rw [Nat.odd_iff] at ho; omega) h4
  refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [← pow_add]
  congr 1
  obtain ⟨k, hk⟩ := hall p hp
  omega

/-- The key quadratic-residue obstruction: a number `N ≡ 3 [MOD 4]` cannot divide `m + 1`
for a perfect square `m`, since otherwise `-1` would be a square modulo `N`. -/
theorem not_sq_of_three_mod_four_dvd_succ {m N k t : ℕ} (hN3 : N % 4 = 3) (hNodd : Odd N)
    (hsq : m = k * k) (hNt : N * t = m + 1) : False := by
  have hcast : (N : ℤ) * (t : ℤ) = (m : ℤ) + 1 := by exact_mod_cast hNt
  have hdvd : (N : ℤ) ∣ (m : ℤ) - (-1 : ℤ) := ⟨(t : ℤ), by linarith⟩
  have hmod : ((m : ℤ)) % (N : ℤ) = (-1 : ℤ) % (N : ℤ) :=
    Int.modEq_iff_dvd.mpr (by simpa using hdvd.neg_right)
  have h1 : jacobiSym (m : ℤ) N = jacobiSym (-1) N := jacobiSym.mod_left' hmod
  rw [jacobiSym.at_neg_one hNodd, ZMod.χ₄_nat_three_mod_four hN3] at h1
  have hcop : Nat.gcd k N = 1 := by
    have h2 : Nat.gcd k N ∣ m + 1 := hNt ▸ Dvd.dvd.mul_right (Nat.gcd_dvd_right k N) t
    have h3 : Nat.gcd k N ∣ m := hsq ▸ Dvd.dvd.mul_left (Nat.gcd_dvd_left k N) k
    exact Nat.dvd_one.mp ((Nat.dvd_add_right h3).mp h2)
  have h4 : jacobiSym ((k : ℤ) ^ 2) N = 1 := jacobiSym.sq_one' (by simpa [Int.gcd] using hcop)
  rw [show ((k : ℤ) ^ 2) = (m : ℤ) by rw [hsq]; push_cast; ring] at h4
  rw [h4] at h1
  exact absurd h1 (by decide)

/-- **Cattaneo's theorem**, first half: every quasiperfect number is odd. -/
theorem Quasiperfect.odd {n : ℕ} (hq : Quasiperfect n) : Odd n := by
  obtain ⟨hn, h⟩ := hq
  rcases Nat.even_or_odd n with he | ho
  swap
  · exact ho
  exfalso
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hm0 : m ≠ 0 := by rintro rfl; simp at hn
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h1
    · simp at he; exact absurd he (by simpa [Nat.even_iff, Nat.odd_iff] using hm)
    · exact h1
  set S := ∑ d ∈ m.divisors, d with hSdef
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have hsig : ∑ d ∈ (2 ^ a * m).divisors, d = (2 ^ (a + 1) - 1) * S := by
    rw [sum_divisors_mul_of_coprime hcop, sum_divisors_two_pow]
  rw [hsig] at h
  set N := 2 ^ (a + 1) - 1 with hN
  have hpow : 2 ^ (a + 1) = N + 1 := by
    have : 1 ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
    omega
  have hN3 : N % 4 = 3 := by
    have h4 : (4 : ℕ) ∣ 2 ^ (a + 1) := by
      have : (2 : ℕ) ^ 2 ∣ 2 ^ (a + 1) := pow_dvd_pow 2 (by omega)
      simpa using this
    omega
  have hNodd : Odd N := by rw [Nat.odd_iff]; omega
  have hkey : N * S = N * m + (m + 1) := by
    have hrw : 2 * (2 ^ a * m) + 1 = 2 ^ (a + 1) * m + 1 := by ring
    rw [hrw, hpow] at h
    rw [h]; ring
  have hSm : m ≤ S := by
    apply Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i)
    simp [Nat.mem_divisors, hm0]
  obtain ⟨t, ht⟩ : ∃ t, S = m + t := ⟨S - m, by omega⟩
  have hNt : N * t = m + 1 := by rw [ht] at hkey; nlinarith [hkey]
  have hSodd : Odd S := by
    have hodd : Odd (N * S) := by rw [h]; exact ⟨2 ^ a * m, by ring⟩
    exact (Nat.odd_mul.mp hodd).2
  obtain ⟨k, hk⟩ := isSquare_of_odd_sigma hm0 hm hSodd
  exact not_sq_of_three_mod_four_dvd_succ hN3 hNodd hk hNt

/-- **Cattaneo's theorem**, second half: every quasiperfect number is a perfect square. -/
theorem Quasiperfect.isSquare {n : ℕ} (hq : Quasiperfect n) : IsSquare n := by
  obtain ⟨hn, h⟩ := hq
  refine isSquare_of_odd_sigma hn.ne' (Quasiperfect.odd ⟨hn, h⟩) ?_
  rw [h]
  exact ⟨n, by ring⟩

/-- `1` is not quasiperfect. -/
theorem not_quasiperfect_one : ¬ Quasiperfect 1 := by
  rintro ⟨-, h⟩
  simp at h

/-- No prime power is quasiperfect. -/
theorem not_quasiperfect_prime_pow {p e : ℕ} (hp : p.Prime) : ¬ Quasiperfect (p ^ e) := by
  intro hq
  have hodd : Odd (p ^ e) := hq.odd
  obtain ⟨hn, h⟩ := hq
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with rfl | hpo
    · rcases Nat.eq_zero_or_pos e with rfl | he
      · simp at h
      · exact absurd (hodd.of_dvd_nat (dvd_pow_self 2 he.ne')) (by decide)
    · have h2 := hp.two_le
      rw [Nat.odd_iff] at hpo
      omega
  rw [Nat.sum_divisors_prime_pow hp] at h
  have hz : ((∑ x ∈ Finset.range (e + 1), (p : ℤ) ^ x)) * ((p : ℤ) - 1) = (p : ℤ) ^ (e + 1) - 1 :=
    geom_sum_mul _ _
  have hcast : (∑ x ∈ Finset.range (e + 1), (p : ℤ) ^ x) = 2 * (p : ℤ) ^ e + 1 := by
    exact_mod_cast congrArg (fun x : ℕ => (x : ℤ)) h
  rw [hcast] at hz
  have hpe : (1 : ℤ) ≤ (p : ℤ) ^ e := one_le_pow₀ (by exact_mod_cast Nat.one_le_of_lt hp3)
  have hp3' : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  have hsucc : (p : ℤ) ^ (e + 1) = (p : ℤ) * (p : ℤ) ^ e := by ring
  nlinarith [hz, hpe, hp3']

/-- **Main reduction.**  A quasiperfect number exists if and only if there is an odd `k > 1`
which is not a prime power and whose square is quasiperfect.  In other words, any quasiperfect
number is necessarily the square of such a `k` (Cattaneo, 1951).  Whether a quasiperfect number
exists at all is an open problem, so this is a conditional reduction, not an existence proof. -/
theorem QuasiperfectExists :
    (∃ n : ℕ, Quasiperfect n) ↔
      ∃ k : ℕ, Odd k ∧ 1 < k ∧ (¬ ∃ p e : ℕ, p.Prime ∧ k = p ^ e) ∧ Quasiperfect (k ^ 2) := by
  constructor
  · rintro ⟨n, hq⟩
    obtain ⟨k, hk⟩ := hq.isSquare
    have hodd := hq.odd
    have hn1 : n ≠ 1 := by rintro rfl; exact not_quasiperfect_one hq
    have hk2 : n = k ^ 2 := by rw [hk]; ring
    have hqk : Quasiperfect (k ^ 2) := hk2 ▸ hq
    refine ⟨k, (Nat.odd_mul.mp (hk ▸ hodd)).1, ?_, ?_, hqk⟩
    · rcases Nat.lt_or_ge k 2 with hlt | hge
      · interval_cases k <;> simp_all
      · omega
    · rintro ⟨p, e, hp, rfl⟩
      exact not_quasiperfect_prime_pow (p := p) (e := e * 2) hp (by simpa [pow_mul] using hqk)
  · rintro ⟨k, -, -, -, hq⟩
    exact ⟨k ^ 2, hq⟩

end Brockian.QuasiperfectNumbers

