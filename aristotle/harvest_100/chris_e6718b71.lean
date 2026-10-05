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
open scoped ArithmeticFunction.sigma

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open Finset ArithmeticFunction

/-- `IsBetrothedPair m n` says that `(m, n)` is a betrothed (quasi-amicable) pair:
two distinct positive integers each of whose sum of divisors equals `m + n + 1`;
equivalently, the sum of the proper divisors of each member is the other member plus one. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

lemma IsBetrothedPair.symm {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothedPair n m := by
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  refine ⟨hn, hm, hne.symm, ?_, ?_⟩ <;> omega

/-- The sum of divisors of a prime `p` is `p + 1`. -/
lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  rw [sigma_one_apply, hp.divisors]
  rw [Finset.sum_insert (by
    simp only [Finset.mem_singleton]
    exact fun h => hp.ne_one h.symm), Finset.sum_singleton]
  omega

/-- Crude bound: twice the sum of divisors of `q` is at most `q * (q + 1)`. -/
lemma two_mul_sigma_one_le (q : ℕ) : 2 * σ 1 q ≤ q * (q + 1) := by
  have hsub : q.divisors ⊆ Finset.range (q + 1) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2) hd.1))
  have hle : σ 1 q ≤ ∑ i ∈ Finset.range (q + 1), i := by
    rw [sigma_one_apply]
    exact Finset.sum_le_sum_of_subset hsub
  have hg : (∑ i ∈ Finset.range (q + 1), i) * 2 = q * (q + 1) := by
    simpa [Nat.mul_comm] using Finset.sum_range_id_mul_two (q + 1)
  omega

/-- The parity of `∑_{i < k} p ^ i` for odd `p` is the parity of `k`. -/
lemma geom_sum_mod_two {p : ℕ} (hp : Odd p) (k : ℕ) :
    (∑ i ∈ Finset.range k, p ^ i) % 2 = k % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hpk : p ^ k % 2 = 1 := Nat.odd_iff.mp hp.pow
      rw [Finset.sum_range_succ]
      omega

/-- If a prime power `p ^ a` has sum of divisors `p ^ a + n + 1` with `n` positive, then
`a = k + 1` for some `k ≥ 1` and the partner `n` equals `p * ∑_{i<k} p ^ i`. -/
lemma partner_eq {p a n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (h1 : σ 1 (p ^ a) = p ^ a + n + 1) :
    ∃ k, 1 ≤ k ∧ a = k + 1 ∧ n = p * ∑ i ∈ Finset.range k, p ^ i := by
  have hsig : σ 1 (p ^ a) = ∑ i ∈ Finset.range (a + 1), p ^ i := by
    rw [sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  rw [hsig, Finset.sum_range_succ] at h1
  have hsum : ∑ i ∈ Finset.range a, p ^ i = n + 1 := by omega
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hsum
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  rw [Finset.sum_range_succ'] at hsum
  have hmul : ∑ i ∈ Finset.range k, p ^ (i + 1) = p * ∑ i ∈ Finset.range k, p ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hmul] at hsum
  simp only [pow_zero] at hsum
  refine ⟨k, ?_, rfl, by omega⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp at hsum; omega
  · exact hk

/-- The only positive solution of `3 σ(u) = 4 u + 3` is `u = 9`. -/
lemma eq_nine_of_sigma_rel {u : ℕ} (hupos : 0 < u) (key : 3 * σ 1 u = 4 * u + 3) : u = 9 := by
  have hsig3 : σ 1 3 = 4 := by rw [sigma_one_apply]; decide
  have h3u : 3 ∣ u :=
    Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) (⟨σ 1 u - 1, by omega⟩ : (3 : ℕ) ∣ 4 * u)
  obtain ⟨d, hd⟩ := h3u
  have hu3 : 3 < u := by
    rcases Nat.lt_or_ge u 4 with h | h
    · have hu' : u = 3 := by omega
      rw [hu', hsig3] at key
      omega
    · exact h
  have hune : u ≠ 0 := by omega
  have hdne1 : d ≠ 1 := by omega
  have hdneu : d ≠ u := by omega
  have h1neu : (1 : ℕ) ≠ u := by omega
  have hT : ({1, d, u} : Finset ℕ) ⊆ u.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨one_dvd u, hune⟩
    · exact Nat.mem_divisors.mpr ⟨⟨3, by omega⟩, hune⟩
    · exact Nat.mem_divisors.mpr ⟨dvd_rfl, hune⟩
  have hsumT : ∑ x ∈ ({1, d, u} : Finset ℕ), x = 1 + d + u := by
    rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨fun h => hdne1 h.symm, h1neu⟩),
      Finset.sum_insert (by simpa using hdneu), Finset.sum_singleton]
    omega
  have h3mem : (3 : ℕ) ∈ ({1, d, u} : Finset ℕ) := by
    by_contra hc
    have hlt : ∑ x ∈ ({1, d, u} : Finset ℕ), x < ∑ x ∈ u.divisors, x :=
      Finset.sum_lt_sum_of_subset hT (Nat.mem_divisors.mpr ⟨⟨d, by omega⟩, hune⟩) hc
        (by norm_num) (fun j _ _ => Nat.zero_le j)
    rw [hsumT, ← sigma_one_apply] at hlt
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at h3mem
  omega

/-- The base `2` is impossible: `2 ^ a` is never a member of a betrothed pair. -/
lemma not_two_pow {a n : ℕ} (h : IsBetrothedPair (2 ^ a) n) : False := by
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  obtain ⟨k, hk1, rfl, hnk⟩ := partner_eq Nat.prime_two hn h1
  obtain ⟨u, hu⟩ : ∃ u, u = ∑ i ∈ Finset.range k, 2 ^ i := ⟨_, rfl⟩
  rw [← hu] at hnk
  have hu2 : u + 1 = 2 ^ k := by
    rw [hu]
    simpa using (Nat.geomSum_eq (le_refl 2) k).symm
  have hupos : 0 < u := by
    have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
    omega
  have huodd : u % 2 = 1 := by
    have h2k : 2 ^ k % 2 = 0 := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp [pow_succ]
    omega
  have hcop : Nat.Coprime 2 u := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega
  have hsig2 : ∑ d ∈ (2 : ℕ).divisors, d = 3 := by decide
  have hsn : σ 1 (2 * u) = 3 * σ 1 u := by
    rw [sigma_one_apply, sigma_one_apply, hcop.sum_divisors_mul, hsig2]
  rw [hnk, hsn] at h2
  have hpow : 2 ^ (k + 1) = 2 * u + 2 := by rw [pow_succ]; omega
  have key : 3 * σ 1 u = 4 * u + 3 := by omega
  have hu9 : u = 9 := eq_nine_of_sigma_rel hupos key
  -- `2 ^ k = 10` is impossible
  have h2k : 2 ^ k = 10 := by omega
  have hk4 : k ≤ 3 := by
    by_contra hc
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> omega

/-- **Hagis–Lord, Proposition 4.**  If a prime power `p ^ a` is a member of a betrothed
(quasi-amicable) pair, then `p` is odd, the exponent `a` is odd and greater than `3`, and the
partner is even. -/
theorem primePower_member_structure {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) :
    Odd p ∧ Odd a ∧ 3 < a ∧ Even n := by
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with rfl | hodd
    · exact absurd (not_two_pow ⟨hm, hn, hne, h1, h2⟩) (fun x => x)
    · exact hodd
  obtain ⟨k, hk1, rfl, hnk⟩ := partner_eq hp hn h1
  obtain ⟨B, hB⟩ : ∃ B, B = ∑ i ∈ Finset.range k, p ^ i := ⟨_, rfl⟩
  rw [← hB] at hnk
  -- `B` is coprime to `p`
  have hcop : Nat.Coprime p B := by
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hBv : B = 1 + p * ∑ i ∈ Finset.range j, p ^ i := by
      rw [hB, hj, Finset.sum_range_succ', Finset.mul_sum]
      simp [pow_succ, mul_comm, Nat.add_comm]
    rw [hBv]
    exact Nat.Coprime.add_mul_left_right (Nat.coprime_one_right p)
      (∑ i ∈ Finset.range j, p ^ i)
  -- σ(n) = (p+1) σ(B), which is even
  have hsn : σ 1 (p * B) = (p + 1) * σ 1 B := by
    rw [sigma_one_apply, sigma_one_apply, hcop.sum_divisors_mul, ← sigma_one_apply,
      sigma_one_prime hp]
  have hpodd' : p % 2 = 1 := Nat.odd_iff.mp hpodd
  have hpk : p ^ (k + 1) % 2 = 1 := Nat.odd_iff.mp hpodd.pow
  have hneven : Even n := by
    rw [hnk, hsn] at h2
    have hev : 2 ∣ (p + 1) * σ 1 B := Dvd.dvd.mul_right ⟨(p + 1) / 2, by omega⟩ _
    rw [Nat.even_iff]
    omega
  -- hence `B` is even, so `k` is even and `a = k + 1` is odd
  have hBeven : B % 2 = 0 := by
    have hn2 : n % 2 = 0 := Nat.even_iff.mp hneven
    rw [hnk] at hn2
    rcases Nat.even_or_odd B with hb | hb
    · exact Nat.even_iff.mp hb
    · exfalso
      have hpb : (p * B) % 2 = 1 := by
        rw [Nat.mul_mod, hpodd', Nat.odd_iff.mp hb]
      omega
  have hkeven : k % 2 = 0 := by
    have := geom_sum_mod_two hpodd k
    omega
  have haodd : Odd (k + 1) := by
    rw [Nat.odd_iff]; omega
  -- exclude `a = 3`, i.e. `k = 2`
  have hk2 : k ≠ 2 := by
    rintro rfl
    have hBv : B = 1 + p := by
      rw [hB]
      simp [Finset.sum_range_succ]
    rw [hnk, hsn, hBv] at h2
    have hcancel : σ 1 (1 + p) = p ^ 2 + 1 := by
      have hp1 : 0 < p + 1 := by omega
      have hexp : p ^ (2 + 1) = p ^ 2 * p := by ring
      have hmul : (p + 1) * σ 1 (1 + p) = (p + 1) * (p ^ 2 + 1) := by nlinarith [h2, hexp]
      exact Nat.eq_of_mul_eq_mul_left hp1 hmul
    have hbound := two_mul_sigma_one_le (1 + p)
    rw [hcancel] at hbound
    have hp3 : p ≤ 3 := by nlinarith
    have hp2 : 2 ≤ p := hp.two_le
    interval_cases p
    · omega
    · rw [show (1 : ℕ) + 3 = 4 from rfl, sigma_one_apply] at hcancel
      revert hcancel
      decide
  exact ⟨hpodd, haodd, by omega, hneven⟩

/-- Both members of a betrothed pair cannot be prime powers. -/
theorem not_both_primePow {p a q b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : IsBetrothedPair (p ^ a) (q ^ b)) : False := by
  obtain ⟨-, -, -, heven⟩ := primePower_member_structure hp h
  obtain ⟨hqodd, -, -, -⟩ := primePower_member_structure hq h.symm
  have hdvd : (2 : ℕ) ∣ q ^ b := heven.two_dvd
  have hq2 : q = 2 :=
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd)).symm
  rw [hq2] at hqodd
  simp [Nat.odd_iff] at hqodd

end Brockian.BetrothedNumbers

