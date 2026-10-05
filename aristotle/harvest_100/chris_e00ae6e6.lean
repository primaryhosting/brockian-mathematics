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

namespace Brockian
namespace BetrothedNumbers

open Finset
open scoped ArithmeticFunction.sigma

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive, they are distinct,
and the sum of the divisors of each, other than the number itself and `1`, gives the other;
equivalently `σ m = σ n = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

lemma IsBetrothedPair.symm {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothedPair n m := by
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  refine ⟨hn, hm, hne.symm, ?_, ?_⟩ <;> omega

/-! ### Basic `σ` computations -/

lemma sigma_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    σ 1 (p ^ a) = ∑ i ∈ range (a + 1), p ^ i := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow hp]

lemma geom_split (p k : ℕ) :
    ∑ i ∈ range (k + 1), p ^ i = 1 + p * ∑ i ∈ range k, p ^ i := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm, add_comm]

lemma coprime_prime_geom {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Nat.Coprime p (∑ i ∈ range (k + 1), p ^ i) := by
  rw [Nat.Prime.coprime_iff_not_dvd hp, geom_split]
  intro hdvd
  have : p ∣ 1 := (Nat.dvd_add_right (Dvd.intro _ rfl)).mp (by rwa [add_comm] at hdvd)
  exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.mp this)

lemma sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have := sigma_prime_pow hp 1
  simpa [Finset.sum_range_succ, add_comm] using this

lemma sigma_prime_mul {p B : ℕ} (hp : p.Prime) (h : Nat.Coprime p B) :
    σ 1 (p * B) = (p + 1) * σ 1 B := by
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h, sigma_prime hp]

/-- Crude upper bound: `2 σ(N) ≤ N (N+1)`. -/
lemma two_mul_sigma_le (N : ℕ) : 2 * σ 1 N ≤ N * (N + 1) := by
  have hsub : N.divisors ⊆ range (N + 1) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2) hd.1))
  have h1 : σ 1 N ≤ ∑ i ∈ range (N + 1), i := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact Finset.sum_le_sum_of_subset hsub
  have h2 : (∑ i ∈ range (N + 1), i) * 2 = (N + 1) * N := Finset.sum_range_id_mul_two (N + 1)
  have h3 : N * (N + 1) = (N + 1) * N := Nat.mul_comm _ _
  omega

/-- If `q = 3 r` with `r ≥ 4`, then `1, 3, r, 3r` are four distinct divisors of `q`, so
`σ(q) ≥ 4r + 4`. -/
lemma sigma_three_mul_ge {r : ℕ} (hr : 4 ≤ r) : 4 * r + 4 ≤ σ 1 (3 * r) := by
  have hq : 3 * r ≠ 0 := by omega
  have hsub : ({1, 3, r, 3 * r} : Finset ℕ) ⊆ (3 * r).divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Nat.mem_divisors]
    refine ⟨?_, hq⟩
    rcases hx with h | h | h | h <;> subst h
    · exact one_dvd _
    · exact Dvd.intro r rfl
    · exact Dvd.intro_left 3 rfl
    · exact dvd_rfl
  have hsum : ∑ x ∈ ({1, 3, r, 3 * r} : Finset ℕ), x = 4 * r + 4 := by
    rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
      Finset.sum_singleton]
    omega
  calc 4 * r + 4 = ∑ x ∈ ({1, 3, r, 3 * r} : Finset ℕ), x := hsum.symm
    _ ≤ ∑ x ∈ (3 * r).divisors, x := Finset.sum_le_sum_of_subset hsub
    _ = σ 1 (3 * r) := (ArithmeticFunction.sigma_one_apply _).symm

/-- For odd `p`, the geometric sum `1 + p + ⋯ + p^{t-1}` has the parity of `t`. -/
lemma geom_parity {p : ℕ} (hp : Odd p) (t : ℕ) :
    (∑ i ∈ range t, p ^ i) % 2 = t % 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ, Nat.add_mod, ih]
      have : p ^ t % 2 = 1 := Nat.odd_iff.mp hp.pow
      omega

lemma two_pow_geom (t : ℕ) : (∑ i ∈ range t, 2 ^ i) + 1 = 2 ^ t := by
  induction t with
  | zero => simp
  | succ t ih => rw [Finset.sum_range_succ]; omega

/-! ### Structure of a prime-power member -/

/-- If `p ^ a` belongs to a betrothed pair with partner `n`, then `a ≥ 2` and
`n = p + p² + ⋯ + p^{a-1}`. -/
lemma partner_form {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) :
    ∃ k : ℕ, a = k + 2 ∧ n = p * ∑ i ∈ range (k + 1), p ^ i := by
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  match a with
  | 0 => simp at h1
  | 1 =>
      rw [sigma_prime_pow hp 1] at h1
      simp [Finset.sum_range_succ, pow_one] at h1
      omega
  | (k + 2) =>
      refine ⟨k, rfl, ?_⟩
      rw [sigma_prime_pow hp (k + 2), Finset.sum_range_succ, geom_split] at h1
      omega

/-- The key numerical obstruction in the case `p = 2`. -/
lemma no_large_two_case {q : ℕ} (hq : 15 ≤ q) (hkey : 3 * σ 1 q = 4 * q + 3) : False := by
  have h3 : q % 3 = 0 := by omega
  obtain ⟨r, hr⟩ : ∃ r, q = 3 * r := ⟨q / 3, by omega⟩
  have hr4 : 4 ≤ r := by omega
  have hbig := sigma_three_mul_ge hr4
  rw [← hr] at hbig
  omega

lemma prime_ne_two {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) : p ≠ 2 := by
  rintro rfl
  obtain ⟨k, rfl, rfl⟩ := partner_form hp h
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  have hodd : (∑ i ∈ range (k + 1), 2 ^ i) % 2 = 1 := by rw [geom_split]; omega
  have hcop : Nat.Coprime 2 (∑ i ∈ range (k + 1), 2 ^ i) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (fun hd => by omega)
  rw [sigma_prime_mul Nat.prime_two hcop] at h2
  have hpow : (∑ i ∈ range (k + 1), 2 ^ i) + 1 = 2 ^ (k + 1) := two_pow_geom (k + 1)
  have hpow2 : (2 : ℕ) ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
  have hkey : 3 * σ 1 (∑ i ∈ range (k + 1), 2 ^ i) = 4 * (∑ i ∈ range (k + 1), 2 ^ i) + 3 := by
    omega
  match k with
  | 0 => norm_num [Finset.sum_range_succ] at hkey
  | 1 =>
      norm_num [Finset.sum_range_succ] at hkey
      rw [show σ 1 3 = 4 by decide] at hkey
      omega
  | 2 =>
      norm_num [Finset.sum_range_succ] at hkey
      rw [show σ 1 7 = 8 by decide] at hkey
      omega
  | (k + 3) =>
      refine no_large_two_case ?_ hkey
      have h : ∑ i ∈ range 4, (2 : ℕ) ^ i ≤ ∑ i ∈ range (k + 3 + 1), 2 ^ i :=
        Finset.sum_le_sum_of_subset (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
      simpa [Finset.sum_range_succ] using h

lemma exponent_odd {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) : Odd a := by
  have hp2 : Odd p := hp.odd_of_ne_two (prime_ne_two hp h)
  obtain ⟨k, rfl, rfl⟩ := partner_form hp h
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  rw [Nat.odd_iff]
  by_contra hcon
  have hk : k % 2 = 0 := by omega
  -- the partner is odd, hence `σ` of it is odd, contradicting evenness of `p + 1`
  have hB : (∑ i ∈ range (k + 1), p ^ i) % 2 = 1 := by rw [geom_parity hp2]; omega
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp hp2
  have hn2 : (p * ∑ i ∈ range (k + 1), p ^ i) % 2 = 1 := by
    rw [Nat.mul_mod, hpodd, hB]
  have hm2 : p ^ (k + 2) % 2 = 1 := Nat.odd_iff.mp hp2.pow
  rw [sigma_prime_mul hp (coprime_prime_geom hp k)] at h2
  have hev : ((p + 1) * σ 1 (∑ i ∈ range (k + 1), p ^ i)) % 2 = 0 := by
    have hp1 : (p + 1) % 2 = 0 := by omega
    rw [Nat.mul_mod, hp1, Nat.zero_mul, Nat.zero_mod]
  omega

lemma partner_even {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) : Even n := by
  have hp2 : Odd p := hp.odd_of_ne_two (prime_ne_two hp h)
  have hao : Odd a := exponent_odd hp h
  obtain ⟨k, rfl, rfl⟩ := partner_form hp h
  have hk : k % 2 = 1 := by
    rw [Nat.odd_iff] at hao; omega
  have hB : (∑ i ∈ range (k + 1), p ^ i) % 2 = 0 := by rw [geom_parity hp2]; omega
  rw [Nat.even_iff, Nat.mul_mod, hB]
  simp

lemma exponent_ne_three {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) : a ≠ 3 := by
  have hp2 : p ≠ 2 := prime_ne_two hp h
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rintro rfl
  obtain ⟨k, hk, hn⟩ := partner_form hp h
  have hk1 : k = 1 := by omega
  subst hk1
  obtain ⟨hm, hpos, hne, h1, h2⟩ := h
  subst hn
  rw [sigma_prime_mul hp (coprime_prime_geom hp 1)] at h2
  have hB : ∑ i ∈ range (1 + 1), p ^ i = p + 1 := by
    simp [Finset.sum_range_succ, add_comm]
  rw [hB] at h2
  -- `(p+1) * σ(p+1) = (p+1) * (p²+1)`
  have hfac : p ^ 3 + p * (p + 1) + 1 = (p + 1) * (p ^ 2 + 1) := by ring
  rw [hfac] at h2
  have hcancel : σ 1 (p + 1) = p ^ 2 + 1 :=
    Nat.eq_of_mul_eq_mul_left (by omega) h2
  have hbound := two_mul_sigma_le (p + 1)
  rw [hcancel] at hbound
  have hple : p ≤ 3 := by nlinarith
  have : p = 3 := by omega
  subst this
  rw [show σ 1 (3 + 1) = 7 by decide] at hcancel
  norm_num at hcancel

/-- **Hagis–Lord, Proposition 4.** If a prime power `p ^ a` is a member of a betrothed
(quasi-amicable) pair with partner `n`, then `p` is odd, the exponent `a` is odd and larger
than `3`, and the partner `n` is even. -/
theorem primePower_member_structure {p a n : ℕ} (hp : p.Prime)
    (h : IsBetrothedPair (p ^ a) n) :
    Odd p ∧ Odd a ∧ 3 < a ∧ Even n := by
  refine ⟨hp.odd_of_ne_two (prime_ne_two hp h), exponent_odd hp h, ?_, partner_even hp h⟩
  obtain ⟨k, hk, -⟩ := partner_form hp h
  have h3 := exponent_ne_three hp h
  have := exponent_odd hp h
  rw [Nat.odd_iff] at this
  omega

/-- Consequently, the two members of a betrothed pair cannot both be prime powers. -/
theorem not_both_primePower {p a q b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : IsBetrothedPair (p ^ a) (q ^ b)) : False := by
  have h1 : Even (q ^ b) := (primePower_member_structure hp h).2.2.2
  have h2 : Odd q := (primePower_member_structure hq h.symm).1
  have h3 : Odd (q ^ b) := h2.pow
  exact (Nat.not_odd_iff_even.mpr h1) h3

end BetrothedNumbers
end Brockian

