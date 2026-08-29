import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Nat
open scoped ArithmeticFunction.sigma
open ArithmeticFunction

namespace Brockian.BetrothedNumbers

/-- `IsBetrothedPair m n` says that `(m, n)` is a betrothed (quasi-amicable) pair:
two distinct positive integers each of whose sum of divisors equals `m + n + 1`,
equivalently, the sum of the nontrivial proper divisors of each equals the other. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

lemma IsBetrothedPair.symm {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothedPair n m := by
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  exact ⟨hn, hm, hne.symm, by omega, by omega⟩

/-- The notion is not vacuous: `(48, 75)` is a betrothed pair. -/
example : IsBetrothedPair 48 75 := ⟨by norm_num, by norm_num, by norm_num, by decide, by decide⟩

/-! ### Basic facts about `σ` on prime powers -/

/-- `σ 1 p = p + 1` for a prime `p`. -/
lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have := sigma_one_apply_prime_pow (p := p) (i := 1) hp
  simpa [Finset.sum_range_succ, add_comm] using this

/-- Splitting off the top and bottom terms of the geometric sum `σ 1 (p ^ (b + 2))`. -/
lemma sigma_one_primePow_add_two {p : ℕ} (hp : p.Prime) (b : ℕ) :
    σ 1 (p ^ (b + 2)) = p ^ (b + 2) + p * σ 1 (p ^ b) + 1 := by
  rw [sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp, Finset.sum_range_succ',
    Finset.sum_range_succ, Finset.mul_sum]
  ring_nf

/-- A prime `p` is coprime to `σ 1 (p ^ b)`. -/
lemma coprime_sigma_one_primePow {p : ℕ} (hp : p.Prime) (b : ℕ) :
    Nat.Coprime p (σ 1 (p ^ b)) := by
  have h : σ 1 (p ^ b) = p * (∑ k ∈ Finset.range b, p ^ k) + 1 := by
    rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ', Finset.mul_sum]
    ring_nf
  rw [h]
  simp

/-- Multiplicativity of `σ` at `p * t` with `p` prime coprime to `t`. -/
lemma sigma_one_prime_mul {p t : ℕ} (hp : p.Prime) (h : Nat.Coprime p t) :
    σ 1 (p * t) = (p + 1) * σ 1 t := by
  rw [isMultiplicative_sigma.map_mul_of_coprime h, sigma_one_prime hp]

/-- `σ 1 (2 ^ b) = 2 ^ (b + 1) - 1`, in additive form. -/
lemma sigma_one_two_pow (b : ℕ) : σ 1 (2 ^ b) + 1 = 2 ^ (b + 1) := by
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  induction b with
  | zero => simp
  | succ c ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- Parity of `σ 1 (p ^ b)` for odd `p`: it is congruent to `b + 1` mod `2`. -/
lemma sigma_one_primePow_mod_two {p : ℕ} (hp : p.Prime) (hodd : Odd p) (b : ℕ) :
    σ 1 (p ^ b) % 2 = (b + 1) % 2 := by
  rw [sigma_one_apply_prime_pow hp]
  induction b with
  | zero => simp
  | succ c ih =>
    rw [Finset.sum_range_succ]
    have hpow : p ^ (c + 1) % 2 = 1 := Nat.odd_iff.mp (hodd.pow)
    omega

/-! ### Upper and lower bounds for `σ` -/

/-- Crude Gauss bound: `2 * σ 1 k ≤ k * (k + 1)`. -/
lemma two_mul_sigma_one_le {k : ℕ} : 2 * σ 1 k ≤ k * (k + 1) := by
  rw [sigma_one_apply]
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · have hsub : k.divisors ⊆ Finset.range (k + 1) := by
      intro d hd
      exact Finset.mem_range.2 (Nat.lt_succ_of_le
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) (Nat.dvd_of_mem_divisors hd)))
    have h1 : ∑ d ∈ k.divisors, d ≤ ∑ d ∈ Finset.range (k + 1), d :=
      Finset.sum_le_sum_of_subset hsub
    have h2 := Finset.sum_range_id_mul_two (k + 1)
    simp only [Nat.add_sub_cancel] at h2
    have h3 : (k + 1) * k = k * (k + 1) := mul_comm _ _
    omega

/-- Lower bound from the four distinct divisors `1, 3, s, 3 * s` of `3 * s`, for `s ≥ 5`. -/
lemma sigma_one_three_mul_ge {s : ℕ} (hs : 5 ≤ s) : 4 * s + 4 ≤ σ 1 (3 * s) := by
  have hsub : ({1, 3, s, 3 * s} : Finset ℕ) ⊆ (3 * s).divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact Nat.mem_divisors.2 ⟨one_dvd _, by omega⟩
    · exact Nat.mem_divisors.2 ⟨⟨s, rfl⟩, by omega⟩
    · exact Nat.mem_divisors.2 ⟨⟨3, by ring⟩, by omega⟩
    · exact Nat.mem_divisors.2 ⟨dvd_rfl, by omega⟩
  have hsum : ∑ d ∈ ({1, 3, s, 3 * s} : Finset ℕ), d = 4 * s + 4 := by
    rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
      Finset.sum_insert (by simp; omega), Finset.sum_singleton]
    omega
  rw [sigma_one_apply]
  calc 4 * s + 4 = ∑ d ∈ ({1, 3, s, 3 * s} : Finset ℕ), d := hsum.symm
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

/-! ### Structure of a prime power member -/

/-- If a prime power `p ^ a` belongs to a betrothed pair with partner `n`, then `a = b + 2`
for some `b`, and `n = p * σ 1 (p ^ b)`. -/
lemma primePower_partner {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) :
    ∃ b : ℕ, a = b + 2 ∧ n = p * σ 1 (p ^ b) := by
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  match a with
  | 0 => simp at h1
  | 1 => rw [pow_one, sigma_one_prime hp] at h1; omega
  | (b + 2) =>
    refine ⟨b, rfl, ?_⟩
    rw [sigma_one_primePow_add_two hp b] at h1
    omega

/-- The prime of a prime power member of a betrothed pair is odd. -/
lemma primePower_member_prime_odd {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) :
    Odd p := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  case inr => exact hodd
  exfalso
  obtain ⟨b, hab, hnb⟩ := primePower_partner hp h
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  set t := σ 1 (2 ^ b) with ht
  have hcop : Nat.Coprime 2 t := coprime_sigma_one_primePow Nat.prime_two b
  have hpow : t + 1 = 2 ^ (b + 1) := sigma_one_two_pow b
  have hpow' : (2 : ℕ) ^ (b + 1) = 2 * 2 ^ b := by ring
  have htodd : t % 2 = 1 := by omega
  have hsig : σ 1 n = 3 * σ 1 t := by
    rw [hnb, sigma_one_prime_mul Nat.prime_two hcop]
  have hpow2 : (2 : ℕ) ^ a = 2 * (t + 1) := by rw [hab, hpow]; ring
  have key : 3 * σ 1 t = 4 * t + 3 := by rw [hsig, hpow2, hnb] at h2; omega
  have h3t : t % 3 = 0 := by omega
  obtain ⟨s, hs⟩ : ∃ s, t = 3 * s := ⟨t / 3, by omega⟩
  have hst : σ 1 t = 4 * s + 1 := by rw [hs] at key ⊢; omega
  have hs0 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with rfl | hpos
    · omega
    · exact hpos
  rcases Nat.lt_or_ge s 5 with hlt | hge
  · interval_cases s
    · have ht3 : t = 3 := by omega
      rw [ht3] at hst; revert hst; decide
    · omega
    · -- `t = 9` would force `2 ^ (b + 1) = 10`
      have h10 : (10 : ℕ) = 2 ^ (b + 1) := by omega
      have h5 : (5 : ℕ) ∣ 2 ^ (b + 1) := ⟨2, by omega⟩
      have := Nat.Prime.dvd_of_dvd_pow (p := 5) (by norm_num) h5
      omega
    · omega
  · rw [hs] at hst
    have := sigma_one_three_mul_ge hge
    omega

/-- The partner of an odd prime power member is even. -/
lemma primePower_member_partner_even {p a n : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : IsBetrothedPair (p ^ a) n) : Even n := by
  obtain ⟨b, hab, hnb⟩ := primePower_partner hp h
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  have hcop := coprime_sigma_one_primePow hp b
  have hsig : σ 1 n = (p + 1) * σ 1 (σ 1 (p ^ b)) := by
    rw [hnb, sigma_one_prime_mul hp hcop]
  obtain ⟨c, hc⟩ : ∃ c, p + 1 = 2 * c := by
    obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩
  have hprod : (p + 1) * σ 1 (σ 1 (p ^ b)) = 2 * (c * σ 1 (σ 1 (p ^ b))) := by
    rw [hc]; ring
  have hpa : p ^ a % 2 = 1 := Nat.odd_iff.mp hodd.pow
  rw [Nat.even_iff]
  omega

/-- The exponent of a prime power member is odd. -/
lemma primePower_member_exponent_odd {p a n : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : IsBetrothedPair (p ^ a) n) : Odd a := by
  obtain ⟨b, hab, hnb⟩ := primePower_partner hp h
  have hn : Even n := primePower_member_partner_even hp hodd h
  rw [hnb] at hn
  rcases Nat.even_mul.mp hn with h' | h'
  · exact absurd h' (Nat.not_even_iff_odd.mpr hodd)
  · have hpar := sigma_one_primePow_mod_two hp hodd b
    have := Nat.even_iff.mp h'
    rw [Nat.odd_iff]
    omega

/-- The exponent of a prime power member is not `3`. -/
lemma primePower_member_exponent_ne_three {p n : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : IsBetrothedPair (p ^ 3) n) : False := by
  obtain ⟨b, hab, hnb⟩ := primePower_partner hp h
  have hb : b = 1 := by omega
  subst hb
  rw [pow_one, sigma_one_prime hp] at hnb
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  have hcop : Nat.Coprime p (p + 1) := by simp
  have hsig : σ 1 n = (p + 1) * σ 1 (p + 1) := by rw [hnb, sigma_one_prime_mul hp hcop]
  have h3 : (p + 1) * σ 1 (p + 1) = (p + 1) * (p ^ 2 + 1) := by
    rw [← hsig, h2, hnb]; ring
  have hcancel : σ 1 (p + 1) = p ^ 2 + 1 := Nat.eq_of_mul_eq_mul_left (by omega) h3
  have hbound := two_mul_sigma_one_le (k := p + 1)
  rw [hcancel] at hbound
  have hple : p ≤ 3 := by nlinarith
  have hp2 : p ≠ 2 := by rintro rfl; exact (Nat.not_odd_iff_even.mpr (by decide)) hodd
  have hp3 : p = 3 := by have := hp.two_le; omega
  subst hp3
  revert hcancel
  decide

/-- **Hagis–Lord, Proposition 4.** If a prime power `p ^ a` is a member of a betrothed
(quasi-amicable) pair with partner `n`, then `p` is odd, `a` is odd with `a > 3`, and the
partner `n` is even. -/
theorem primePower_member_structure {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) :
    Odd p ∧ Odd a ∧ 3 < a ∧ Even n := by
  have hpodd : Odd p := primePower_member_prime_odd hp h
  have haodd : Odd a := primePower_member_exponent_odd hp hpodd h
  have hn : Even n := primePower_member_partner_even hp hpodd h
  refine ⟨hpodd, haodd, ?_, hn⟩
  obtain ⟨b, hb, -⟩ := primePower_partner hp h
  rcases Nat.lt_or_ge 3 a with h3 | h3
  · exact h3
  · exfalso
    have ha3 : a = 3 := by
      obtain ⟨k, hk⟩ := haodd
      omega
    subst ha3
    exact primePower_member_exponent_ne_three hp hpodd h

/-- Both members of a betrothed pair cannot be prime powers. -/
theorem not_both_primePower {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : IsBetrothedPair (p ^ a) (q ^ b)) : False := by
  have h1 := primePower_member_structure hp h
  have h2 := primePower_member_structure hq h.symm
  -- `q ^ b` is even, so `q = 2`, contradicting oddness of `q`
  have hqe : Even (q ^ b) := h1.2.2.2
  have hq2 : Even q := (Nat.even_pow.mp hqe).1
  exact (Nat.not_odd_iff_even.mpr hq2) h2.1

end Brockian.BetrothedNumbers

