import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction Finset

namespace Brockian
namespace BetrothedNumbers

/-- `IsBetrothedPair m n` says that `(m, n)` is a betrothed (quasi-amicable) pair: two distinct
positive integers, each of whose sum of divisors equals `m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

theorem IsBetrothedPair.symm {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothedPair n m := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h2, h1, h3.symm, ?_, ?_⟩
  · rw [h5]; ring
  · rw [h4]; ring

/-- The smallest betrothed pair; in particular the definition is not vacuous. -/
theorem isBetrothedPair_48_75 : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

/-! ### Elementary auxiliary lemmas -/

/-- Peeling the first term off a geometric sum. -/
theorem geom_sum_succ_eq (p m : ℕ) :
    ∑ k ∈ range (m + 1), p ^ k = p * (∑ k ∈ range m, p ^ k) + 1 := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

/-- A geometric sum of an odd base has the parity of its number of terms. -/
theorem geom_sum_mod_two {p : ℕ} (hp : p % 2 = 1) (m : ℕ) :
    (∑ k ∈ range m, p ^ k) % 2 = m % 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hp]
      simp [Nat.add_mod]

theorem two_geom_sum (m : ℕ) : (∑ k ∈ range m, 2 ^ k) + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ]; omega

/-- The crude bound `σ(k) ≤ k(k+1)/2`, coming from `divisors k ⊆ {0, …, k}`. -/
theorem two_mul_sigma_one_le (k : ℕ) : 2 * sigma 1 k ≤ k * (k + 1) := by
  have h1 : sigma 1 k = ∑ d ∈ k.divisors, d := sigma_one_apply k
  have h2 : k.divisors ⊆ range (k + 1) := fun d hd =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.divisor_le hd))
  have h3 : ∑ d ∈ k.divisors, d ≤ ∑ d ∈ range (k + 1), d :=
    Finset.sum_le_sum_of_subset h2
  have h4 : (∑ i ∈ range (k + 1), i) * 2 = (k + 1) * k := by
    simpa using Finset.sum_range_id_mul_two (k + 1)
  have h5 : k * (k + 1) = (k + 1) * k := Nat.mul_comm _ _
  omega

theorem sigma_one_prime {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  have := sigma_one_apply_prime_pow (p := p) (i := 1) hp
  simp [Finset.sum_range_succ] at this
  omega

/-- If `n` is odd and `σ n` is odd, then `n` is a perfect square. -/
theorem exists_sq_of_odd_sigma_one :
    ∀ n : ℕ, n % 2 = 1 → sigma 1 n % 2 = 1 → ∃ r, n = r * r := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hodd hs
    have hn0 : n ≠ 0 := by rintro rfl; simp at hodd
    by_cases hn1 : n = 1
    · exact ⟨1, by simp [hn1]⟩
    · obtain ⟨q, e, t, hq, hsplit, hcop, he1⟩ :
          ∃ q e t : ℕ, q.Prime ∧ q ^ e * t = n ∧ Nat.Coprime (q ^ e) t ∧ 1 ≤ e :=
        ⟨n.minFac, n.factorization n.minFac, n / n.minFac ^ (n.factorization n.minFac),
          Nat.minFac_prime hn1, Nat.ordProj_mul_ordCompl_eq_self n n.minFac,
          (Nat.coprime_ordCompl (Nat.minFac_prime hn1) hn0).pow_left _,
          Nat.Prime.factorization_pos_of_dvd (Nat.minFac_prime hn1) hn0 (Nat.minFac_dvd n)⟩
      have hq2 : q % 2 = 1 := by
        rcases hq.eq_two_or_odd with h | h
        · subst h
          exfalso
          have : 2 ∣ n := hsplit ▸ dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) t
          omega
        · exact h
      have ht0 : 0 < t := by
        rcases Nat.eq_zero_or_pos t with rfl | h
        · simp at hsplit; omega
        · exact h
      have hmul : sigma 1 n = sigma 1 (q ^ e) * sigma 1 t := by
        rw [← hsplit]
        exact isMultiplicative_sigma.map_mul_of_coprime hcop
      have hpe : sigma 1 (q ^ e) % 2 = (e + 1) % 2 := by
        rw [sigma_one_apply_prime_pow hq, geom_sum_mod_two hq2]
      have hodds : Odd (sigma 1 (q ^ e)) ∧ Odd (sigma 1 t) := by
        rw [← Nat.odd_mul, ← hmul, Nat.odd_iff]; exact hs
      have h2 : sigma 1 t % 2 = 1 := Nat.odd_iff.mp hodds.2
      have he : e % 2 = 0 := by
        have := Nat.odd_iff.mp hodds.1; omega
      have htodd : t % 2 = 1 := by
        rcases Nat.even_or_odd t with h | h
        · exfalso
          have h2t : 2 ∣ t := h.two_dvd
          have : 2 ∣ n := hsplit ▸ Dvd.dvd.mul_left h2t _
          omega
        · exact Nat.odd_iff.mp h
      have hqe : 2 ≤ q ^ e := by
        calc 2 ≤ q := hq.two_le
        _ = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ e := Nat.pow_le_pow_right (by omega) he1
      have htlt : t < n := by
        rw [← hsplit]
        calc t = 1 * t := (one_mul t).symm
        _ < q ^ e * t := (Nat.mul_lt_mul_right ht0).mpr (by omega)
      obtain ⟨r, hr⟩ := ih t htlt htodd h2
      refine ⟨q ^ (e / 2) * r, ?_⟩
      have hqq : q ^ (e / 2) * q ^ (e / 2) = q ^ e := by
        rw [← pow_add]; congr 1; omega
      rw [← hsplit, hr, ← hqq]; ring

/-! ### Structure of a prime power member -/

/-- **Hagis–Lord, Proposition 4.** If a prime power `p ^ a` (with `a ≥ 1`) is a member of a
betrothed (quasi-amicable) pair, then `p` is odd, the exponent `a` is odd and greater than `3`,
and the partner is even. -/
theorem primePower_member_structure {p a n : ℕ} (hp : p.Prime) (ha : 0 < a)
    (h : IsBetrothedPair (p ^ a) n) :
    Odd p ∧ Odd a ∧ 3 < a ∧ Even n := by
  obtain ⟨hm0, hn0, hne, hsm, hsn⟩ := h
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [sigma_one_apply_prime_pow hp] at hsm
  set u := ∑ k ∈ range b, p ^ k with hu
  have hstep : ∑ k ∈ range (b + 1 + 1), p ^ k = p * u + 1 + p ^ (b + 1) := by
    rw [Finset.sum_range_succ, geom_sum_succ_eq]
  rw [hstep] at hsm
  -- the partner is `n = p * u` with `u = 1 + p + ⋯ + p ^ (b-1)`
  have hnu : n = p * u := by omega
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [hu] at hnu; omega
    · exact hb
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have huw : u = p * (∑ k ∈ range c, p ^ k) + 1 := by rw [hu, geom_sum_succ_eq]
  have hcop : Nat.Coprime p u := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    rw [huw] at hd
    have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_right p _)).mp hd
    have := Nat.le_of_dvd one_pos h1
    have := hp.two_le
    omega
  have hsigman : sigma 1 n = (p + 1) * sigma 1 u := by
    rw [hnu, isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_prime hp]
  -- `p` is odd
  have hp2 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with hp2 | hp2
    · exfalso
      subst hp2
      have hu1 : u + 1 = 2 ^ (c + 1) := by rw [hu]; exact two_geom_sum (c + 1)
      have h2c : 2 ^ (c + 1) % 2 = 0 := by
        have : (2:ℕ) ^ (c + 1) = 2 * 2 ^ c := by ring
        omega
      have huodd : u % 2 = 1 := by omega
      have hpa : 2 ^ (c + 1 + 1) % 2 = 0 := by
        have : (2:ℕ) ^ (c + 1 + 1) = 2 * 2 ^ (c + 1) := by ring
        omega
      have hsnodd : sigma 1 n % 2 = 1 := by omega
      have hsu : sigma 1 u % 2 = 1 := by
        rw [hsigman, Nat.mul_mod] at hsnodd
        omega
      obtain ⟨r, hr⟩ := exists_sq_of_odd_sigma_one u huodd hsu
      rcases Nat.eq_zero_or_pos c with rfl | hc
      · have hu1' : u = 1 := by simp [hu]
        have h2 : sigma 1 2 = 3 := by decide
        rw [hnu, hu1'] at hsn
        norm_num [h2] at hsn
      · have h4 : (2:ℕ) ^ (c + 1) = 4 * 2 ^ (c - 1) := by
          rw [show c + 1 = 2 + (c - 1) by omega, pow_add]
          norm_num
        have hu4 : u % 4 = 3 := by omega
        have hrr : r * r % 4 = r % 4 * (r % 4) % 4 := Nat.mul_mod r r 4
        have hlt : r % 4 < 4 := Nat.mod_lt _ (by norm_num)
        interval_cases h : r % 4 <;> omega
    · exact hp2
  -- the partner is even, and the exponent is odd
  have hp1 : (p + 1) % 2 = 0 := by omega
  have hpar : sigma 1 n % 2 = 0 := by rw [hsigman, Nat.mul_mod, hp1, zero_mul]; simp
  have hpa : p ^ (c + 1 + 1) % 2 = 1 := by rw [Nat.pow_mod, hp2]; simp
  have hn2 : n % 2 = 0 := by omega
  have hu2 : u % 2 = 0 := by
    rw [hnu] at hn2
    simp [Nat.mul_mod, hp2] at hn2
    omega
  have hc2 : c % 2 = 1 := by
    rw [hu, geom_sum_mod_two hp2] at hu2
    omega
  -- the exponent is not `3`
  have hc1 : c ≠ 1 := by
    intro hc
    subst hc
    have hu' : u = p + 1 := by rw [hu]; simp [Finset.sum_range_succ]; omega
    have h1 : sigma 1 n = (p + 1) * sigma 1 (p + 1) := by rw [hsigman, hu']
    have h2 : sigma 1 n = (p + 1) * (p * p + 1) := by
      rw [hsn, hnu, hu']; ring
    have hkey : sigma 1 (p + 1) = p * p + 1 :=
      Nat.eq_of_mul_eq_mul_left (by omega) (h1 ▸ h2)
    have hb := two_mul_sigma_one_le (p + 1)
    rw [hkey] at hb
    have hple : p ≤ 3 := by nlinarith [hp.two_le]
    have hp3 : p = 3 := by have := hp.two_le; omega
    subst hp3
    have h7 : sigma 1 (3 + 1) = 7 := by decide
    omega
  refine ⟨Nat.odd_iff.mpr hp2, Nat.odd_iff.mpr (by omega), by omega, Nat.even_iff.mpr hn2⟩

/-- Both members of a betrothed pair cannot be prime powers. -/
theorem not_both_primePower {p a q b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ha : 0 < a) (hb : 0 < b) (h : IsBetrothedPair (p ^ a) (q ^ b)) : False := by
  obtain ⟨-, -, -, hqb⟩ := primePower_member_structure hp ha h
  obtain ⟨hqodd, -, -, -⟩ := primePower_member_structure hq hb h.symm
  rw [Nat.even_pow] at hqb
  have h1 : q % 2 = 0 := Nat.even_iff.mp hqb.1
  have h2 : q % 2 = 1 := Nat.odd_iff.mp hqodd
  omega

end BetrothedNumbers
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

