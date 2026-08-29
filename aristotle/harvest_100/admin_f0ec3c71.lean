/-
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian.BetrothedNumbers

open ArithmeticFunction
open scoped ArithmeticFunction
/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive and distinct, and
the sum of the divisors of each, other than the number itself and `1`, is the other member;
equivalently `sigma m = sigma n = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ ArithmeticFunction.sigma 1 m = m + n + 1 ∧
    ArithmeticFunction.sigma 1 n = m + n + 1

/-! ### Auxiliary arithmetic facts -/

/-- The sum of divisors of a prime power is the geometric sum. -/
theorem sigma_one_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ArithmeticFunction.sigma 1 (p ^ e) = ∑ i ∈ Finset.range (e + 1), p ^ i := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow hp]

/-- A geometric sum of powers of an odd number has the parity of the number of terms. -/
theorem sum_pow_mod_two {p : ℕ} (hp : Odd p) (m : ℕ) :
    (∑ i ∈ Finset.range m, p ^ i) % 2 = m % 2 := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, Nat.add_mod, ih]
      have : p ^ k % 2 = 1 := Nat.odd_iff.mp hp.pow
      omega

theorem geom_sum_two (b : ℕ) : (∑ i ∈ Finset.range b, 2 ^ i) + 1 = 2 ^ b := by
  induction b with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
      omega

theorem sq_mod_four_ne_three (t : ℕ) : t * t % 4 ≠ 3 := by
  rcases Nat.even_or_odd t with ⟨s, hs⟩ | ⟨s, hs⟩ <;> subst hs
  · have : (s + s) * (s + s) = 4 * (s * s) := by ring
    omega
  · have : (2 * s + 1) * (2 * s + 1) = 4 * (s * s + s) + 1 := by ring
    omega

/-- Crude bound: `2 σ n ≤ n (n + 1)`, since every divisor of `n` lies in `[1, n]`. -/
theorem two_mul_sum_Icc (n : ℕ) : 2 * ∑ d ∈ Finset.Icc 1 n, d = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), Nat.mul_add, ih]; ring

theorem two_mul_sigma_one_le (n : ℕ) : 2 * ArithmeticFunction.sigma 1 n ≤ n * (n + 1) := by
  rw [ArithmeticFunction.sigma_one_apply]
  have hsub : n.divisors ⊆ Finset.Icc 1 n := by
    intro d hd
    simp only [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne', Nat.divisor_le hd⟩
  calc 2 * ∑ d ∈ n.divisors, d ≤ 2 * ∑ d ∈ Finset.Icc 1 n, d :=
        Nat.mul_le_mul_left 2 (Finset.sum_le_sum_of_subset hsub)
    _ = n * (n + 1) := two_mul_sum_Icc n

/-- If `n` is odd and `σ n` is odd, then `n` is a perfect square. -/
theorem isSquare_of_odd_sigma_one :
    ∀ n : ℕ, n ≠ 0 → Odd n → Odd (ArithmeticFunction.sigma 1 n) → IsSquare n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn0 hodd hsig
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hn0) with h1 | h1
    · exact ⟨1, by omega⟩
    · have hq : (n.minFac).Prime := Nat.minFac_prime (by omega)
      set q := n.minFac with hqdef
      set e := n.factorization q with hedef
      set m := n / q ^ e with hmdef
      have hsplit : q ^ e * m = n := Nat.ordProj_mul_ordCompl_eq_self n q
      have hcop : Nat.Coprime (q ^ e) m :=
        Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hq hn0)
      have hm0 : m ≠ 0 := (Nat.ordCompl_pos q hn0).ne'
      have hsigmul : ArithmeticFunction.sigma 1 n
          = ArithmeticFunction.sigma 1 (q ^ e) * ArithmeticFunction.sigma 1 m := by
        rw [← hsplit]
        exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
      rw [hsigmul] at hsig
      obtain ⟨hs1, hs2⟩ := Nat.odd_mul.mp hsig
      have hqodd : Odd q := hodd.of_dvd_nat (Nat.minFac_dvd n)
      have he : Even e := by
        rw [sigma_one_prime_pow hq, Nat.odd_iff] at hs1
        have h2 := sum_pow_mod_two hqodd (e + 1)
        rw [Nat.even_iff]
        omega
      have hmodd : Odd m := hodd.of_dvd_nat (Nat.ordCompl_dvd n q)
      have hmlt : m < n := by
        have hepos : 0 < e := Nat.Prime.factorization_pos_of_dvd hq hn0 (Nat.minFac_dvd n)
        have hqe : 1 < q ^ e := Nat.one_lt_pow hepos.ne' hq.one_lt
        calc m = 1 * m := (one_mul m).symm
          _ < q ^ e * m := Nat.mul_lt_mul_of_lt_of_le hqe (le_refl m) (Nat.pos_of_ne_zero hm0)
          _ = n := hsplit
      obtain ⟨t, ht⟩ := ih m hmlt hm0 hmodd hs2
      obtain ⟨k, hk⟩ := he
      exact ⟨q ^ k * t, by rw [← hsplit, ht, hk]; ring⟩

/-! ### The structure of a prime power member -/

/-- If `p ^ a` belongs to a betrothed pair with partner `n`, then `a = b + 1` with `b ≥ 1`,
`n = p (1 + p + ⋯ + p ^ (b-1))`, and `p` does not divide that geometric sum. -/
theorem partner_of_prime_pow {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) :
    ∃ b : ℕ, a = b + 1 ∧ 1 ≤ b ∧ n = p * (∑ i ∈ Finset.range b, p ^ i) ∧
      ¬ p ∣ (∑ i ∈ Finset.range b, p ^ i) := by
  obtain ⟨hm0, hn0, hne, hsm, hsn⟩ := h
  rw [sigma_one_prime_pow hp, Finset.sum_range_succ] at hsm
  have hsum : ∑ i ∈ Finset.range a, p ^ i = n + 1 := by omega
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := by
    cases a with
    | zero => simp at hsum
    | succ k => exact ⟨k, rfl⟩
  rw [geom_sum_succ] at hsum
  have hb : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp at hsum; omega
    · exact hb
  refine ⟨b, rfl, hb, by omega, ?_⟩
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  rw [geom_sum_succ]
  intro hdvd
  have h1 : p ∣ 1 := (Nat.dvd_add_right ⟨_, rfl⟩).mp hdvd
  have h2 := Nat.dvd_one.mp h1
  have h3 := hp.two_le
  omega

theorem sigma_one_four : ArithmeticFunction.sigma 1 4 = 7 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, sigma_one_prime_pow Nat.prime_two]
  decide

/-- **Hagis–Lord, Proposition 4.**  If a prime power `p ^ a` is a member of a betrothed
(quasi-amicable) pair, then `p` is odd, the exponent `a` is odd and greater than `3`, and the
partner `n` is even. -/
theorem primePower_member_structure {p a n : ℕ} (hp : p.Prime)
    (h : IsBetrothedPair (p ^ a) n) :
    Odd p ∧ Odd a ∧ 3 < a ∧ Even n := by
  obtain ⟨b, rfl, hb1, hnT, hpT⟩ := partner_of_prime_pow hp h
  obtain ⟨hm0, hn0, hne, hsm, hsn⟩ := h
  set T := ∑ i ∈ Finset.range b, p ^ i with hT
  have hT0 : T ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at hnT
    omega
  have hcopT : Nat.Coprime p T := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpT
  have hsigmaN : ArithmeticFunction.sigma 1 n
      = ArithmeticFunction.sigma 1 p * ArithmeticFunction.sigma 1 T := by
    rw [hnT]
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopT
  have hsigp : ArithmeticFunction.sigma 1 p = p + 1 := by
    have h1 := sigma_one_prime_pow hp 1
    rw [pow_one] at h1
    rw [h1]
    simp [Finset.sum_range_succ]
    omega
  -- Step 1: `p` is odd.
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with rfl | hodd
    · exfalso
      have hTodd : Odd T := Nat.odd_iff.mpr (by omega)
      have hsigTodd : Odd (ArithmeticFunction.sigma 1 T) := by
        have hodd : Odd (ArithmeticFunction.sigma 1 n) := by
          rw [hsn, Nat.odd_iff]
          have h2 : (2 : ℕ) ^ (b + 1) = 2 * 2 ^ b := by ring
          omega
        rw [hsigmaN, hsigp] at hodd
        exact (Nat.odd_mul.mp hodd).2
      obtain ⟨t, ht⟩ := isSquare_of_odd_sigma_one T hT0 hTodd hsigTodd
      have hpow := geom_sum_two b
      rw [← hT] at hpow
      rcases Nat.lt_or_ge b 2 with hb | hb
      · -- b = 1, so T = 1 and n = 2
        have hb' : b = 1 := by omega
        subst hb'
        have : T = 1 := by omega
        rw [this] at hnT
        rw [hnT] at hsn
        rw [show ArithmeticFunction.sigma 1 (2 * 1) = ArithmeticFunction.sigma 1 2 by norm_num,
          hsigp] at hsn
        norm_num at hsn
      · -- b ≥ 2, so T ≡ 3 mod 4, impossible for a square
        obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
        have h4 : (2 : ℕ) ^ (c + 2) = 4 * 2 ^ c := by ring
        have hT4 : T % 4 = 3 := by omega
        rw [ht] at hT4
        exact sq_mod_four_ne_three t hT4
    · exact hodd
  -- Step 2: `T` is even (equivalently, `n` is even).
  have hTeven : Even T := by
    by_contra hcon
    have hTodd : Odd T := Nat.not_even_iff_odd.mp hcon
    have hnodd : Odd n := by rw [hnT]; exact hpodd.mul hTodd
    have hsigNodd : Odd (ArithmeticFunction.sigma 1 n) := by
      rw [hsn, Nat.odd_iff]
      have h1 : (p ^ (b + 1)) % 2 = 1 := Nat.odd_iff.mp hpodd.pow
      have h2 : n % 2 = 1 := Nat.odd_iff.mp hnodd
      omega
    obtain ⟨t, ht⟩ := isSquare_of_odd_sigma_one n (by omega) hnodd hsigNodd
    have hpn : p ∣ n := ⟨T, hnT⟩
    have hpt : p ∣ t := by
      refine hp.dvd_of_dvd_pow (n := 2) ?_
      rw [pow_two, ← ht]
      exact hpn
    obtain ⟨s, rfl⟩ := hpt
    have hmul : p * T = p * (p * (s * s)) := by rw [← hnT, ht]; ring
    exact hpT ⟨p * (s * s) / p * 1, by
      have := Nat.eq_of_mul_eq_mul_left hp.pos hmul
      simpa [Nat.mul_div_cancel_left _ hp.pos] using this⟩
  have hneven : Even n := by rw [hnT]; exact hTeven.mul_left p
  -- Step 3: `b` is even, hence `a = b + 1` is odd.
  have hbeven : Even b := by
    have h1 := sum_pow_mod_two hpodd b
    rw [← hT] at h1
    rw [Nat.even_iff]
    rw [Nat.even_iff] at hTeven
    omega
  have haodd : Odd (b + 1) := by
    rw [Nat.odd_iff]
    rw [Nat.even_iff] at hbeven
    omega
  -- Step 4: `b ≠ 2`, so `b ≥ 4` and `a = b + 1 > 3`.
  have hb2 : b ≠ 2 := by
    rintro rfl
    have hTval : T = 1 + p := by
      rw [hT]
      simp [Finset.sum_range_succ]
    have hsigT : ArithmeticFunction.sigma 1 T = p ^ 2 + 1 := by
      have h1 : ArithmeticFunction.sigma 1 n = (p + 1) * ArithmeticFunction.sigma 1 T := by
        rw [hsigmaN, hsigp]
      rw [hsn, hnT] at h1
      have h2 : p ^ (2 + 1) + p * T + 1 = (p + 1) * (p ^ 2 + 1) := by
        rw [hTval]; ring
      rw [h2] at h1
      exact (Nat.eq_of_mul_eq_mul_left (show 0 < p + 1 by omega) h1).symm
    have hbound := two_mul_sigma_one_le T
    rw [hsigT, hTval] at hbound
    have hple : p ≤ 3 := by nlinarith [hp.two_le]
    have hp3 : p = 3 := by
      have h2 := hp.two_le
      have h3 := Nat.odd_iff.mp hpodd
      omega
    rw [hp3] at hsigT hTval
    rw [hTval] at hsigT
    norm_num [sigma_one_four] at hsigT
  refine ⟨hpodd, haodd, ?_, hneven⟩
  rw [Nat.even_iff] at hbeven
  omega

/-- **Corollary.** The two members of a betrothed pair cannot both be prime powers. -/
theorem not_both_primePower {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : IsBetrothedPair (p ^ a) (q ^ b)) : False := by
  obtain ⟨-, -, -, hqeven⟩ := primePower_member_structure hp h
  obtain ⟨hm0, hn0, hne, hsm, hsn⟩ := h
  have h' : IsBetrothedPair (q ^ b) (p ^ a) := by
    refine ⟨hn0, hm0, hne.symm, ?_, ?_⟩ <;> omega
  obtain ⟨hqodd, -, -, -⟩ := primePower_member_structure hq h'
  have h1 : Odd (q ^ b) := hqodd.pow
  rw [Nat.odd_iff] at h1
  rw [Nat.even_iff] at hqeven
  omega

end Brockian.BetrothedNumbers

