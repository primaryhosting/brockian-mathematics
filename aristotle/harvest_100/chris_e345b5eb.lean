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

import Mathlib

/-!
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace QuasiperfectNumbers

open Finset

/-- A positive natural number `n` is *quasiperfect* if the sum of all of its divisors is
`2 * n + 1`, equivalently if the sum of its proper divisors is `n + 1`.

Whether a quasiperfect number exists is a longstanding open problem; no example is known,
and none can be small (see `no_quasiperfect_lt_500`). -/
def Quasiperfect (n : ℕ) : Prop :=
  0 < n ∧ ∑ d ∈ n.divisors, d = 2 * n + 1

theorem quasiperfect_iff_sum_properDivisors {n : ℕ} (hn : 0 < n) :
    Quasiperfect n ↔ ∑ d ∈ n.properDivisors, d = n + 1 := by
  unfold Quasiperfect
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

/-! ### No prime power is quasiperfect -/

/-- A geometric-sum bound: `1 + p + ⋯ + p ^ (k-1) < p ^ k` whenever `2 ≤ p`. -/
theorem geomSum_lt_pow {p : ℕ} (hp : 2 ≤ p) (k : ℕ) : ∑ i ∈ range k, p ^ i < p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hpk : 0 < p ^ k := pow_pos (show 0 < p by omega) k
      nlinarith

/-- No prime power is quasiperfect: in fact `σ (p ^ k) < 2 * p ^ k + 1` for every prime `p`. -/
theorem sum_divisors_prime_pow_ne {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∑ d ∈ (p ^ k).divisors, d ≠ 2 * p ^ k + 1 := by
  have hlt : ∑ d ∈ (p ^ k).divisors, d < 2 * p ^ k + 1 := by
    rw [Nat.sum_divisors_prime_pow hp (f := fun d => d), Finset.sum_range_succ]
    have := geomSum_lt_pow hp.two_le k
    omega
  omega

/-- A quasiperfect number is not a prime power. -/
theorem Quasiperfect.not_isPrimePow {n : ℕ} (h : Quasiperfect n) : ¬ IsPrimePow n := by
  rintro ⟨p, k, hp, -, rfl⟩
  exact sum_divisors_prime_pow_ne (Nat.prime_iff.2 hp) k h.2

/-! ### A quasiperfect number is a square or twice a square -/

/-- Parity through the cast to `ZMod 2`. -/
theorem natCast_zmod_two_eq_one_iff (n : ℕ) : ((n : ZMod 2) = 1) ↔ Odd n := by
  rw [Nat.odd_iff, ← ZMod.natCast_mod n 2]
  have h : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
  interval_cases h2 : (n % 2) <;> simp

/-- For odd `p`, the geometric sum `1 + p + ⋯ + p ^ e` is odd exactly when `e` is even. -/
theorem odd_geomSum_iff {p : ℕ} (hp : Odd p) (e : ℕ) :
    Odd (∑ i ∈ range (e + 1), p ^ i) ↔ Even e := by
  rw [← natCast_zmod_two_eq_one_iff]
  push_cast
  have hp1 : (p : ZMod 2) = 1 := (natCast_zmod_two_eq_one_iff p).2 hp
  simp [hp1]
  exact ZMod.natCast_eq_zero_iff_even

/-- For an odd prime `p`, `σ (p ^ e)` is odd exactly when `e` is even. -/
theorem odd_sum_divisors_prime_pow_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e : ℕ) :
    Odd (∑ d ∈ (p ^ e).divisors, d) ↔ Even e := by
  rw [Nat.sum_divisors_prime_pow hp (f := fun d => d)]
  exact odd_geomSum_iff (hp.odd_of_ne_two hp2) e

/-- The sum-of-divisors function is multiplicative. -/
theorem sum_divisors_mul_of_coprime {a b : ℕ} (h : a.Coprime b) :
    ∑ d ∈ (a * b).divisors, d = (∑ d ∈ a.divisors, d) * (∑ d ∈ b.divisors, d) := by
  simpa [ArithmeticFunction.sigma_one_apply] using
    (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime h

/-- If `σ n` is odd then every odd prime occurs to an even power in `n`. -/
theorem factorization_even_of_odd_sum_divisors {n : ℕ} (hn : n ≠ 0)
    (h : Odd (∑ d ∈ n.divisors, d)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Even (n.factorization p) := by
  by_contra hodd
  have hmem : p ∈ n.primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨hp, ?_, hn⟩
    by_contra hdvd
    exact hodd (by simp [Nat.factorization_eq_zero_of_not_dvd hdvd])
  set f : ℕ → ZMod 2 := fun m => ((∑ d ∈ m.divisors, d : ℕ) : ZMod 2) with hf
  have hkey : f n = n.factorization.prod fun q k => f (q ^ k) := by
    refine Nat.multiplicative_factorization f (fun x y hxy => ?_) (by simp [hf]) hn
    show ((∑ d ∈ (x * y).divisors, d : ℕ) : ZMod 2) = _
    rw [sum_divisors_mul_of_coprime hxy, Nat.cast_mul]
  have hzero : f (p ^ n.factorization p) = 0 := by
    have h1 : ¬ Odd (∑ d ∈ (p ^ n.factorization p).divisors, d) := by
      rw [odd_sum_divisors_prime_pow_iff hp hp2]
      exact hodd
    exact ZMod.natCast_eq_zero_iff_even.2 (Nat.not_odd_iff_even.1 h1)
  have hfn : f n = 0 := by
    rw [hkey]
    exact Finset.prod_eq_zero (by simpa [Nat.support_factorization] using hmem) hzero
  have hfn' : ((∑ d ∈ n.divisors, d : ℕ) : ZMod 2) = 0 := hfn
  rw [(natCast_zmod_two_eq_one_iff _).2 h] at hfn'
  exact one_ne_zero hfn'

/-- A positive natural number all of whose prime exponents are even is a square. -/
theorem sq_of_factorization_even {m : ℕ} (hm : m ≠ 0) (h : ∀ p, Even (m.factorization p)) :
    ∃ t, m = t ^ 2 := by
  refine ⟨∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2), ?_⟩
  rw [← Finset.prod_pow]
  have hcongr : ∀ p ∈ m.primeFactors,
      (p ^ (m.factorization p / 2)) ^ 2 = p ^ m.factorization p := by
    intro p _
    rw [← pow_mul]
    obtain ⟨t, ht⟩ := h p
    congr 1
    omega
  rw [Finset.prod_congr rfl hcongr]
  exact (Nat.factorization_prod_pow_eq_self hm).symm

/-- Any quasiperfect number is a square or twice a square (equivalently, its odd part is a
perfect square). -/
theorem Quasiperfect.sq_or_two_mul_sq {n : ℕ} (h : Quasiperfect n) :
    ∃ k, n = k ^ 2 ∨ n = 2 * k ^ 2 := by
  obtain ⟨hpos, heq⟩ := h
  have hodd : Odd (∑ d ∈ n.divisors, d) := by
    rw [heq]
    exact ⟨n, by ring⟩
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hn0 : (2 : ℕ) ^ a * m ≠ 0 := hpos.ne'
  have hfac : ∀ p, Even (m.factorization p) := by
    intro p
    by_cases hp : p.Prime
    · by_cases hp2 : p = 2
      · subst hp2
        have : ¬ (2 ∣ m) := by
          rw [Nat.two_dvd_ne_zero, ← Nat.odd_iff]
          exact hm
        simp [Nat.factorization_eq_zero_of_not_dvd this]
      · have hkey := factorization_even_of_odd_sum_divisors hn0 hodd hp hp2
        rwa [Nat.factorization_mul (pow_ne_zero _ (two_ne_zero)) hm0, Finsupp.add_apply,
          Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_apply,
          if_neg (Ne.symm hp2), zero_add] at hkey
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  obtain ⟨t, rfl⟩ := sq_of_factorization_even hm0 hfac
  rcases Nat.even_or_odd a with ⟨b, hb⟩ | ⟨b, hb⟩
  · exact ⟨2 ^ b * t, Or.inl (by subst hb; ring)⟩
  · exact ⟨2 ^ b * t, Or.inr (by subst hb; ring)⟩

/-! ### No small quasiperfect numbers -/

set_option maxRecDepth 400000 in
set_option maxHeartbeats 1000000 in
/-- There is no quasiperfect number below `500`. -/
theorem no_quasiperfect_lt_500 {n : ℕ} (hn : n < 500) : ¬ Quasiperfect n := by
  have key : ∀ m ∈ Finset.range 500, ∑ d ∈ m.divisors, d ≠ 2 * m + 1 := by decide
  intro h
  exact key n (Finset.mem_range.2 hn) h.2

/-! ### Main statement -/

/-- **Conditional reduction for the existence of quasiperfect numbers.**

Whether a quasiperfect number (a number `n` with `σ n = 2 * n + 1`) exists is a longstanding
open problem, so we record instead a Lean-checked reduction: a quasiperfect number exists if
and only if there is one that is at least `500`, is not a prime power, is a square or twice a
square, and has proper-divisor sum `n + 1`. -/
theorem QuasiperfectExists :
    (∃ n, Quasiperfect n) ↔
      ∃ n : ℕ, Quasiperfect n ∧ 500 ≤ n ∧ ¬ IsPrimePow n ∧
        (∃ k, n = k ^ 2 ∨ n = 2 * k ^ 2) ∧
        ∑ d ∈ n.properDivisors, d = n + 1 := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, hn, ?_, hn.not_isPrimePow, hn.sq_or_two_mul_sq,
      (quasiperfect_iff_sum_properDivisors hn.1).1 hn⟩
    by_contra hlt
    exact no_quasiperfect_lt_500 (by omega) hn
  · rintro ⟨n, hn, -⟩
    exact ⟨n, hn⟩

end QuasiperfectNumbers
end Brockian

