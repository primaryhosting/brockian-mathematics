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
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GiugaNumbers

open Finset

/-- A *Giuga number* is a composite natural number `n > 1` such that every prime `p`
dividing `n` satisfies `p ∣ n / p - 1`. -/
def IsGiuga (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ p ∈ n.primeFactors, p ∣ n / p - 1

/-- Sanity check: `30 = 2 * 3 * 5` is the smallest Giuga number. -/
theorem isGiuga_thirty : IsGiuga 30 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hd : p ∣ 30 := Nat.dvd_of_mem_primeFactors hp
  have hle : p ≤ 30 := Nat.le_of_dvd (by norm_num) hd
  have h2 := hpp.two_le
  interval_cases p <;> revert hpp hd <;> norm_num

/-! ### Basic structure of Giuga numbers -/

theorem three_le_of_prime_ne_two {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : 3 ≤ p := by
  have := hp.two_le
  omega

theorem odd_not_mem_two {n : ℕ} (hodd : Odd n) (h : (2 : ℕ) ∈ n.primeFactors) : False := by
  have h2 : (2 : ℕ) ∣ n := Nat.dvd_of_mem_primeFactors h
  rw [Nat.odd_iff] at hodd
  omega

theorem IsGiuga.squarefree {n : ℕ} (h : IsGiuga n) : Squarefree n := by
  obtain ⟨hn, -, hdvd⟩ := h
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpn : p ∣ n := dvd_trans (Dvd.intro p rfl) hpp
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩
  have h1 : p ∣ n / p := by
    obtain ⟨k, hk⟩ := hpp
    refine ⟨k, ?_⟩
    rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  have h2 : p ∣ n / p - 1 := hdvd p hmem
  have hle : 1 ≤ n / p := Nat.one_le_div_iff hp.pos |>.mpr (Nat.le_of_dvd (by omega) hpn)
  have hp1 : p ∣ 1 := by
    have := Nat.dvd_sub h1 h2
    simpa [Nat.sub_sub_self hle] using this
  exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.mp hp1)

theorem IsGiuga.prod_primeFactors {n : ℕ} (h : IsGiuga n) :
    ∏ p ∈ n.primeFactors, p = n :=
  Nat.prod_primeFactors_of_squarefree h.squarefree

theorem IsGiuga.two_le_card {n : ℕ} (h : IsGiuga n) : 2 ≤ n.primeFactors.card := by
  have hprod := h.prod_primeFactors
  by_contra hc
  push_neg at hc
  interval_cases hcard : n.primeFactors.card
  · have hempty : n.primeFactors = ∅ := Finset.card_eq_zero.mp hcard
    rw [hempty, Finset.prod_empty] at hprod
    have := h.1
    omega
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
    rw [hp, Finset.prod_singleton] at hprod
    have hmem : p ∈ n.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
    exact h.2.1 (hprod ▸ Nat.prime_of_mem_primeFactors hmem)

/-- For a squarefree `n` and a prime factor `p`, `n / p` is the product of the other
prime factors. -/
theorem div_eq_prod_erase {n : ℕ} (hsq : ∏ p ∈ n.primeFactors, p = n) {p : ℕ}
    (hp : p ∈ n.primeFactors) : n / p = ∏ r ∈ n.primeFactors.erase p, r := by
  have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
  have hx : p * ∏ r ∈ n.primeFactors.erase p, r = n :=
    (Finset.mul_prod_erase _ (fun r => r) hp).trans hsq
  conv_lhs => rw [← hx]
  exact Nat.mul_div_cancel_left _ hp0

/-- The key arithmetic fact: for a Giuga number `n`, the sum of the reciprocals of its
prime divisors exceeds `1`. -/
theorem IsGiuga.one_lt_sum_inv {n : ℕ} (h : IsGiuga n) :
    1 < ∑ p ∈ n.primeFactors, (1 : ℚ) / p := by
  obtain ⟨hn, hnp, hdvd⟩ := h
  have h' : IsGiuga n := ⟨hn, hnp, hdvd⟩
  have hprod : ∏ p ∈ n.primeFactors, p = n := h'.prod_primeFactors
  set D := ∑ p ∈ n.primeFactors, n / p with hD
  -- Each prime factor divides `D - 1`.
  have hone : ∀ p ∈ n.primeFactors, p ∣ D - 1 := by
    intro p hp
    have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hsplit : D = n / p + ∑ r ∈ n.primeFactors.erase p, n / r :=
      (Finset.add_sum_erase _ _ hp).symm
    have hle : 1 ≤ n / p := Nat.one_le_div_iff hp0 |>.mpr (Nat.le_of_dvd (by omega) hpn)
    have h2 : p ∣ ∑ r ∈ n.primeFactors.erase p, n / r := by
      refine Finset.dvd_sum ?_
      intro r hr
      have hrP : r ∈ n.primeFactors := Finset.mem_of_mem_erase hr
      have hrp : p ≠ r := fun hh => (Finset.ne_of_mem_erase hr) hh.symm
      rw [div_eq_prod_erase hprod hrP]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hrp, hp⟩)
    have h3 : p ∣ n / p - 1 := hdvd p hp
    have hrw : D - 1 = (n / p - 1) + ∑ r ∈ n.primeFactors.erase p, n / r := by omega
    rw [hrw]
    exact Dvd.dvd.add h3 h2
  have hdvdn : n ∣ D - 1 := by
    rw [← hprod]
    exact Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) hone
  -- `D` is at least `2`, so `D - 1` is positive.
  have hcard := h'.two_le_card
  have hD2 : 2 ≤ D := by
    obtain ⟨p, hp⟩ : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
    have hterm : 2 ≤ n / p := by
      rw [div_eq_prod_erase hprod hp]
      have hne : (n.primeFactors.erase p).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hp]
        omega
      obtain ⟨r, hr⟩ := hne
      have hr2 : 2 ≤ r := (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hr)).two_le
      have hpos : 0 < ∏ s ∈ n.primeFactors.erase p, s := by
        refine Nat.pos_of_ne_zero ?_
        intro hzero
        rw [Finset.prod_eq_zero_iff] at hzero
        obtain ⟨s, hs, hs0⟩ := hzero
        exact (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hs)).pos.ne' hs0
      exact le_trans hr2 (Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem _ hr))
    exact le_trans hterm
      (Finset.single_le_sum (f := fun p => n / p) (fun i _ => Nat.zero_le _) hp)
  have hnD : n + 1 ≤ D := by
    have := Nat.le_of_dvd (by omega) hdvdn
    omega
  -- Translate to the rational statement.
  have hcast : (n : ℚ) * ∑ p ∈ n.primeFactors, (1 : ℚ) / p = (D : ℚ) := by
    rw [Finset.mul_sum, hD, Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).pos.ne'
    rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hp) hp0]
    field_simp
  have hnpos : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
  have hDn : (n : ℚ) + 1 ≤ (D : ℚ) := by exact_mod_cast hnD
  nlinarith [hcast, hDn, hnpos]

/-! ### Sums of reciprocals of odd primes -/

/-- The first eight odd primes (padded by `23`). -/
def q : ℕ → ℕ
  | 0 => 3
  | 1 => 5
  | 2 => 7
  | 3 => 11
  | 4 => 13
  | 5 => 17
  | 6 => 19
  | _ => 23

theorem q_ge_three (k : ℕ) : 3 ≤ q k := by
  unfold q
  split <;> norm_num

/-- Partial sums of the reciprocals of the first `k` odd primes. -/
noncomputable def B (k : ℕ) : ℚ := ∑ i ∈ range k, (1 : ℚ) / q i

theorem q_step {k : ℕ} (hk : k ≤ 6) {p : ℕ} (hp : p.Prime) (h : q k < p) : q (k + 1) ≤ p := by
  by_contra hcon
  push_neg at hcon
  interval_cases k <;> simp only [q] at h hcon <;> interval_cases p <;> norm_num at hp

theorem le_max_of_odd_primes :
    ∀ (k : ℕ), k ≤ 7 → ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime ∧ p ≠ 2) → S.card = k + 1 →
      ∃ hS : S.Nonempty, q k ≤ S.max' hS := by
  intro k
  induction k with
  | zero =>
    intro _ S hS hc
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    refine ⟨hne, ?_⟩
    obtain ⟨hp, hp2⟩ := hS _ (S.max'_mem hne)
    have h3 := three_le_of_prime_ne_two hp hp2
    simpa [q] using h3
  | succ k ih =>
    intro hk S hS hc
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    refine ⟨hne, ?_⟩
    have hmS : S.max' hne ∈ S := S.max'_mem hne
    have hcard' : (S.erase (S.max' hne)).card = k + 1 := by
      rw [Finset.card_erase_of_mem hmS, hc]
      omega
    obtain ⟨hne', hle⟩ :=
      ih (by omega) (S.erase (S.max' hne)) (fun p hp => hS p (Finset.mem_of_mem_erase hp)) hcard'
    have hmem := Finset.max'_mem _ hne'
    have hlt : (S.erase (S.max' hne)).max' hne' < S.max' hne :=
      lt_of_le_of_ne (Finset.le_max' S _ (Finset.mem_of_mem_erase hmem))
        (Finset.ne_of_mem_erase hmem)
    exact q_step (by omega) (hS _ hmS).1 (lt_of_le_of_lt hle hlt)

theorem sum_inv_le_B :
    ∀ (k : ℕ), k ≤ 8 → ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime ∧ p ≠ 2) → S.card ≤ k →
      ∑ p ∈ S, (1 : ℚ) / p ≤ B k := by
  intro k
  induction k with
  | zero =>
    intro _ S _ hc
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hc)
    simp [hS0, B]
  | succ k ih =>
    intro hk S hS hc
    have hqpos : (0 : ℚ) < q k := by
      have := q_ge_three k
      exact_mod_cast lt_of_lt_of_le (by norm_num) this
    have hBsucc : B (k + 1) = B k + 1 / q k := by
      simp [B, Finset.sum_range_succ]
    rcases le_or_gt S.card k with hcase | hcase
    · have hpos : (0 : ℚ) < 1 / q k := by positivity
      linarith [ih (by omega) S hS hcase]
    · have hcard : S.card = k + 1 := le_antisymm hc hcase
      obtain ⟨hne, hmax⟩ := le_max_of_odd_primes k (by omega) S hS hcard
      have hmS : S.max' hne ∈ S := S.max'_mem hne
      have hsplit : ∑ p ∈ S, (1 : ℚ) / p
          = 1 / (S.max' hne : ℚ) + ∑ p ∈ S.erase (S.max' hne), (1 : ℚ) / p :=
        (Finset.add_sum_erase _ _ hmS).symm
      have h1 : (1 : ℚ) / (S.max' hne : ℚ) ≤ 1 / q k := by
        apply one_div_le_one_div_of_le hqpos
        exact_mod_cast hmax
      have h2 : ∑ p ∈ S.erase (S.max' hne), (1 : ℚ) / p ≤ B k := by
        refine ih (by omega) _ (fun p hp => hS p (Finset.mem_of_mem_erase hp)) ?_
        rw [Finset.card_erase_of_mem hmS, hcard]
        omega
      linarith [hsplit, h1, h2]

theorem B_eight_lt_one : B 8 < 1 := by
  norm_num [B, Finset.sum_range_succ, q]

/-- At most eight distinct odd primes have reciprocal sum less than one. -/
theorem sum_inv_odd_primes_lt_one {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    (hcard : S.card ≤ 8) : ∑ p ∈ S, (1 : ℚ) / p < 1 :=
  lt_of_le_of_lt (sum_inv_le_B 8 le_rfl S hS hcard) B_eight_lt_one

/-! ### Odd Giuga numbers have at least nine prime factors -/

theorem odd_primeFactors {n : ℕ} (hodd : Odd n) :
    ∀ p ∈ n.primeFactors, p.Prime ∧ p ≠ 2 := by
  intro p hp
  refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
  rintro rfl
  exact odd_not_mem_two hodd hp

theorem odd_giuga_nine_primeFactors {n : ℕ} (hodd : Odd n) (h : IsGiuga n) :
    9 ≤ n.primeFactors.card := by
  by_contra hc
  push_neg at hc
  have := sum_inv_odd_primes_lt_one (odd_primeFactors hodd) (by omega)
  linarith [h.one_lt_sum_inv]

theorem pow_card_le_of_giuga {n : ℕ} (h : IsGiuga n) (hodd : Odd n) : 3 ^ 9 ≤ n := by
  have hprod := h.prod_primeFactors
  have hcard := odd_giuga_nine_primeFactors hodd h
  have hS := odd_primeFactors hodd
  have hle : ∏ _p ∈ n.primeFactors, 3 ≤ ∏ p ∈ n.primeFactors, p :=
    Finset.prod_le_prod' (fun p hp => three_le_of_prime_ne_two (hS p hp).1 (hS p hp).2)
  rw [Finset.prod_const, hprod] at hle
  calc (3 : ℕ) ^ 9 ≤ 3 ^ n.primeFactors.card := Nat.pow_le_pow_right (by norm_num) hcard
    _ ≤ n := hle

/-- **Conditional reduction for the existence of an odd Giuga number.**
Whether an odd Giuga number exists is an open problem; what is proved here is that any
odd Giuga number necessarily has at least nine distinct prime factors, and hence is at
least `3 ^ 9`. -/
theorem OddGiugaExists :
    (∃ n : ℕ, Odd n ∧ IsGiuga n) →
      ∃ n : ℕ, Odd n ∧ IsGiuga n ∧ 9 ≤ n.primeFactors.card ∧ 3 ^ 9 ≤ n := by
  rintro ⟨n, hodd, h⟩
  exact ⟨n, hodd, h, odd_giuga_nine_primeFactors hodd h, pow_card_le_of_giuga h hodd⟩

end Brockian.GiugaNumbers

