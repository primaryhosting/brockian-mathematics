import Mathlib

/-!
# Giuga numbers and the open odd-Giuga question

A **Giuga number** is a composite `n > 1` such that for every prime `p` dividing `n`,
`p ∣ (n / p − 1)`.  The smallest is `30 = 2·3·5`; others are `858`, `1722`, `66198`, …

Giuga numbers sit beside perfect numbers as an old aliquot-flavoured problem: it is a
genuinely **OPEN** question whether an **odd** Giuga number exists — exactly parallel to
the odd perfect number problem.  Every known Giuga number is even, and all are squarefree.

This file
* verifies concrete Giuga numbers (`30`, and `858` as a bonus), kernel-checked;
* proves the elementary **necessary condition** that *every* Giuga number is squarefree
  (the same squarefree argument as in the perfect/Lehmer setting: a repeated prime factor
  would force `p ∣ 1`); and
* records the odd-Giuga existence question as an unproven `def`.

It is **not** claimed here that odd Giuga numbers do or do not exist.
-/

namespace Brockian.GiugaNumbers

/-- A Giuga number: composite `n > 1` with `p ∣ (n / p − 1)` for every prime divisor `p`. -/
def GiugaNumber (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ∣ (n / p - 1)

/-- OPEN: does an **odd** Giuga number exist?  Recorded as an unproven `def`, exactly
parallel to the odd perfect number problem; this file does **not** resolve it. -/
def OddGiugaExists : Prop := ∃ n : ℕ, Odd n ∧ GiugaNumber n

/-! ## Concrete verified Giuga numbers -/

/-- FLAGSHIP — `30 = 2·3·5` is a Giuga number.
The prime divisors of `30` are exactly `{2, 3, 5}`, and
`2 ∣ 14`, `3 ∣ 9`, `5 ∣ 5`.  The universally-quantified prime `p` is bounded by
`p ∣ 30 ⇒ p ≤ 30`, after which every case is decidable. -/
theorem giuga_30 : GiugaNumber 30 := by
  refine ⟨by norm_num, by norm_num, fun p hp hpd => ?_⟩
  have hle : p ≤ 30 := Nat.le_of_dvd (by norm_num) hpd
  interval_cases p <;> revert hp hpd <;> decide

/-- BONUS — `858 = 2·3·11·13` is a Giuga number.
Prime divisors `{2, 3, 11, 13}`: `429 − 1 = 428` is `2`-divisible, `286 − 1 = 285` is
`3`-divisible, `78 − 1 = 77` is `11`-divisible, `66 − 1 = 65` is `13`-divisible.
The prime `p` is pinned to one of the four factors via `Nat.Prime.dvd_mul`, avoiding a
`decide` over the full range. -/
theorem giuga_858 : GiugaNumber 858 := by
  refine ⟨by norm_num, by norm_num, fun p hp hpd => ?_⟩
  have h858 : (858 : ℕ) = 2 * (3 * (11 * 13)) := by norm_num
  rw [h858] at hpd
  rcases hp.dvd_mul.1 hpd with h2 | h35
  · have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h2
    subst this; decide
  · rcases hp.dvd_mul.1 h35 with h3 | h1113
    · have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h3
      subst this; decide
    · rcases hp.dvd_mul.1 h1113 with h11 | h13
      · have : p = 11 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h11
        subst this; decide
      · have : p = 13 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h13
        subst this; decide

/-! ## The necessary condition: every Giuga number is squarefree -/

/-- FLAGSHIP NECESSARY CONDITION — every Giuga number is squarefree.

If a prime `p` had `p² ∣ n`, then `p ∣ n / p`, while the Giuga condition gives
`p ∣ (n / p − 1)`.  Subtracting (using `n / p ≥ 1`) yields `p ∣ 1`, impossible for a
prime.  Hence no prime square divides `n`. -/
theorem giugaNumber_squarefree {n : ℕ} (h : GiugaNumber n) : Squarefree n := by
  obtain ⟨hn1, _, hgiuga⟩ := h
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hp2
  -- `hp : Nat.Prime p` (`Nat.Prime` is defeq `Irreducible`); name it explicitly
  have hpnat : p.Prime := hp
  -- `p ∣ n` since `p ∣ p*p ∣ n`
  have hpn : p ∣ n := dvd_trans ⟨p, rfl⟩ hp2
  -- `p ∣ n / p` since `p*p ∣ n`
  have hdvd_div : p ∣ n / p := (Nat.dvd_div_iff_mul_dvd hpn).2 hp2
  -- Giuga condition at the prime `p`
  have hg : p ∣ (n / p - 1) := hgiuga p hpnat hpn
  -- `n / p ≥ 1` because `p ∣ n` and `n > 0`
  have hpos : 1 ≤ n / p := (Nat.one_le_div_iff hpnat.pos).mpr (Nat.le_of_dvd (by omega) hpn)
  -- subtract the two divisibilities: `p ∣ (n/p) − (n/p − 1) = 1`
  have h1 : p ∣ (n / p) - (n / p - 1) := Nat.dvd_sub hdvd_div hg
  have hsub : (n / p) - (n / p - 1) = 1 := by omega
  rw [hsub] at h1
  exact absurd (Nat.dvd_one.mp h1) hpnat.ne_one

lemma GiugaNumber.squarefree {n : ℕ} (h : GiugaNumber n) : Squarefree n := by
  obtain ⟨hn1, -, hdvd⟩ := h
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hcon
  have hpn : p ∣ n := dvd_trans (Dvd.intro p rfl) hcon
  have h1 : p ∣ n / p - 1 := hdvd p hp hpn
  obtain ⟨k, hk⟩ := hcon
  have h2 : p ∣ n / p := ⟨k, by rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]⟩
  have hpos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
  have hone : p ∣ 1 := by
    have := Nat.dvd_sub h2 h1
    rwa [Nat.sub_sub_self hpos] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp hone)

theorem giugaNumber_three_primes {n : ℕ} (h : GiugaNumber n) : 3 ≤ n.primeFactors.card := by
  have hsq := h.squarefree
  obtain ⟨hn1, hnp, hdvd⟩ := h
  have hprod : ∏ p ∈ n.primeFactors, p = n := Nat.prod_primeFactors_of_squarefree hsq
  by_contra hcon
  push_neg at hcon
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn1
  have hpos : 1 ≤ n.primeFactors.card := Finset.card_pos.mpr hne
  interval_cases hc : n.primeFactors.card
  · -- one prime factor: n is prime
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
    have hmem : p ∈ n.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
    have : n = p := by rw [← hprod, hp, Finset.prod_singleton]
    exact hnp (this ▸ (Nat.prime_of_mem_primeFactors hmem))
  · -- two prime factors: n = p * q with p ∣ q - 1 and q ∣ p - 1
    obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp hc
    have hpm : p ∈ n.primeFactors := by rw [hs]; simp
    have hqm : q ∈ n.primeFactors := by rw [hs]; simp
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpm
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hqm
    have hn : n = p * q := by
      rw [← hprod, hs, Finset.prod_pair hpq]
    have hdp : p ∣ q - 1 := by
      have := hdvd p hp (Nat.dvd_of_mem_primeFactors hpm)
      rwa [hn, Nat.mul_div_cancel_left _ hp.pos] at this
    have hdq : q ∣ p - 1 := by
      have := hdvd q hq (Nat.dvd_of_mem_primeFactors hqm)
      rwa [hn, mul_comm, Nat.mul_div_cancel_left _ hq.pos] at this
    have hp2 := hp.two_le
    have hq2 := hq.two_le
    have h1 : p ≤ q - 1 := Nat.le_of_dvd (by omega) hdp
    have h2 : q ≤ p - 1 := Nat.le_of_dvd (by omega) hdq
    omega

theorem not_giugaNumber_prime_pow {p k : ℕ} (hp : p.Prime) : ¬ GiugaNumber (p ^ k) := by
  rintro ⟨h1, h2, h3⟩
  match k with
  | 0 => simp at h1
  | 1 => exact h2 (by simpa using hp)
  | (m + 2) =>
    have hd : p ∣ p ^ (m + 2) := dvd_pow_self p (by omega)
    have hsub := h3 p hp hd
    rw [pow_succ, Nat.mul_div_cancel _ hp.pos] at hsub
    have h4 : p ∣ p ^ (m + 1) := dvd_pow_self p (by omega)
    have h5 : (1 : ℕ) ≤ p ^ (m + 1) := Nat.one_le_pow _ _ hp.pos
    have h6 : p ∣ p ^ (m + 1) - (p ^ (m + 1) - 1) := Nat.dvd_sub h4 hsub
    have h7 : p ^ (m + 1) - (p ^ (m + 1) - 1) = 1 := by omega
    rw [h7] at h6
    exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.mp h6)

end Brockian.GiugaNumbers
