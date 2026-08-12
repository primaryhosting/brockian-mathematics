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
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.GiugaNumbers

/-- A *Giuga number* is a composite natural number `n > 1` such that
`p ∣ n / p - 1` for every prime `p` dividing `n`. -/
def IsGiuga (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ p ∈ n.primeFactors, p ∣ n / p - 1

/-- `30 = 2 * 3 * 5` is a Giuga number. -/
theorem isGiuga_thirty : IsGiuga 30 := by
  have hpf : (30 : ℕ).primeFactors = {2, 3, 5} := by simp [Nat.primeFactors]
  refine ⟨by norm_num, by decide, ?_⟩
  rw [hpf]
  decide

/-- Every Giuga number is squarefree. -/
theorem IsGiuga.squarefree {n : ℕ} (h : IsGiuga n) : Squarefree n := by
  obtain ⟨h1, -, hdvd⟩ := h
  have hn0 : n ≠ 0 := by omega
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpn : p ∣ n := dvd_trans (Dvd.intro p rfl) hpp
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpn, hn0⟩
  have hd1 : p ∣ n / p := by
    rcases hpp with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    subst hc
    rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  have hd2 : p ∣ n / p - 1 := hdvd p hmem
  have hge : 1 ≤ n / p := (Nat.one_le_div_iff hp.pos).2 (Nat.le_of_dvd (by omega) hpn)
  have hone : p ∣ 1 := by
    have := Nat.dvd_sub hd1 hd2
    simpa [Nat.sub_sub_self hge] using this
  exact hp.one_lt.ne' (Nat.dvd_one.1 hone)

/-- For a finite set `S` of primes, dividing `∏ q ∈ S, q` by a member `p` deletes `p`. -/
theorem prod_div_eq_prod_erase {S : Finset ℕ} (hp : ∀ p ∈ S, p.Prime) (p : ℕ) (hpS : p ∈ S) :
    (∏ q ∈ S, q) / p = ∏ q ∈ S.erase p, q := by
  classical
  have h : p * ∏ q ∈ S.erase p, q = ∏ q ∈ S, q := Finset.mul_prod_erase S (fun q => q) hpS
  rw [← h, Nat.mul_div_cancel_left _ (hp p hpS).pos]

/-- Key arithmetic lemma: if `S` is a set of at least two primes such that each `p ∈ S`
divides `(∏ q ∈ S.erase p, q) - 1`, then the sum of the reciprocals of the elements of `S`
exceeds `1`. -/
theorem one_lt_sum_inv_of_dvd_prod_erase {S : Finset ℕ} (hp : ∀ p ∈ S, p.Prime)
    (hcard : 2 ≤ S.card) (hdvd : ∀ p ∈ S, p ∣ (∏ q ∈ S.erase p, q) - 1) :
    1 < ∑ p ∈ S, (p : ℚ)⁻¹ := by
  classical
  set N : ℕ := ∏ p ∈ S, p with hN
  set T : ℕ := ∑ p ∈ S, ∏ q ∈ S.erase p, q with hT
  have hposq : ∀ p ∈ S, 1 ≤ ∏ q ∈ S.erase p, q := by
    intro p hpS
    refine Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 ?_)
    intro q hq
    exact (hp q (Finset.mem_of_mem_erase hq)).ne_zero
  have hT2 : 2 ≤ T := by
    have h := Finset.card_nsmul_le_sum S (fun p => ∏ q ∈ S.erase p, q) 1 hposq
    simp only [smul_eq_mul, mul_one] at h
    omega
  have hqdvd : ∀ q ∈ S, q ∣ T - 1 := by
    intro q hq
    have hsplit : T = (∏ r ∈ S.erase q, r) + ∑ p ∈ S.erase q, ∏ r ∈ S.erase p, r := by
      rw [hT, ← Finset.add_sum_erase _ _ hq]
    have h1 : q ∣ (∏ r ∈ S.erase q, r) - 1 := hdvd q hq
    have h2 : q ∣ ∑ p ∈ S.erase q, ∏ r ∈ S.erase p, r := by
      refine Finset.dvd_sum ?_
      intro p hpe
      have hpq : p ≠ q := (Finset.mem_erase.1 hpe).1
      exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨fun h => hpq h.symm, hq⟩)
    have hge1 : 1 ≤ ∏ r ∈ S.erase q, r := hposq q hq
    have hrw : T - 1 = ((∏ r ∈ S.erase q, r) - 1) + ∑ p ∈ S.erase q, ∏ r ∈ S.erase p, r := by
      omega
    rw [hrw]
    exact Nat.dvd_add h1 h2
  have hNdvd : N ∣ T - 1 :=
    Finset.prod_primes_dvd _ (fun a ha => (hp a ha).prime) hqdvd
  have hNpos : 0 < N := by
    refine Nat.pos_of_ne_zero ?_
    rw [hN]
    exact Finset.prod_ne_zero_iff.2 (fun q hq => (hp q hq).ne_zero)
  have hNT : N < T := by
    have := Nat.le_of_dvd (by omega) hNdvd
    omega
  have hsum : ∑ p ∈ S, (p : ℚ)⁻¹ = (T : ℚ) / (N : ℚ) := by
    rw [hT, hN]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro p hpS
    have hprod : (∏ q ∈ S, (q : ℚ)) = (p : ℚ) * ∏ q ∈ S.erase p, (q : ℚ) :=
      (Finset.mul_prod_erase _ _ hpS).symm
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (hp p hpS).ne_zero
    have hq0 : (∏ q ∈ S.erase p, (q : ℚ)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 (fun q hq => ?_)
      exact Nat.cast_ne_zero.2 (hp q (Finset.mem_of_mem_erase hq)).ne_zero
    rw [hprod]
    field_simp
  rw [hsum, lt_div_iff₀ (by exact_mod_cast hNpos)]
  simpa using (Nat.cast_lt (α := ℚ)).2 hNT

/-- The reciprocals of at most eight distinct odd primes sum to less than `1`. -/
theorem sum_inv_lt_one_of_odd_primes {S : Finset ℕ} (hp : ∀ p ∈ S, p.Prime)
    (h2 : ∀ p ∈ S, p ≠ 2) (hcard : S.card ≤ 8) :
    ∑ p ∈ S, (p : ℚ)⁻¹ < 1 := by
  classical
  set L : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 23} with hL
  set A : Finset ℕ := S.filter (fun p => p < 29) with hA
  set B : Finset ℕ := S.filter (fun p => ¬ p < 29) with hB
  have hAL : A ⊆ L := by
    intro p hpA
    rw [hA, Finset.mem_filter] at hpA
    obtain ⟨hpS, hlt⟩ := hpA
    have hpp := hp p hpS
    have hp2 := h2 p hpS
    have h2le : 2 ≤ p := hpp.two_le
    rw [hL]
    interval_cases p <;> revert hpp hp2 <;> decide
  have hsplit : ∑ p ∈ S, (p : ℚ)⁻¹ = (∑ p ∈ A, (p : ℚ)⁻¹) + ∑ p ∈ B, (p : ℚ)⁻¹ :=
    (Finset.sum_filter_add_sum_filter_not S _ _).symm
  have hBbound : ∑ p ∈ B, (p : ℚ)⁻¹ ≤ (B.card : ℚ) * (1 / 29) := by
    have hmem : ∀ p ∈ B, (p : ℚ)⁻¹ ≤ 1 / 29 := by
      intro p hpB
      rw [hB, Finset.mem_filter] at hpB
      have h29 : (29 : ℚ) ≤ (p : ℚ) := by exact_mod_cast (by omega : 29 ≤ p)
      rw [one_div]
      exact inv_anti₀ (by norm_num) h29
    calc ∑ p ∈ B, (p : ℚ)⁻¹ ≤ B.card • (1 / 29 : ℚ) := Finset.sum_le_card_nsmul B _ _ hmem
      _ = (B.card : ℚ) * (1 / 29) := by simp [nsmul_eq_mul]
  have hLAbound : (B.card : ℚ) * (1 / 23) ≤ ∑ p ∈ L \ A, (p : ℚ)⁻¹ := by
    have hmem : ∀ p ∈ L \ A, (1 / 23 : ℚ) ≤ (p : ℚ)⁻¹ := by
      intro p hpm
      have hpL : p ∈ L := (Finset.mem_sdiff.1 hpm).1
      have hple : 3 ≤ p ∧ p ≤ 23 := by
        rw [hL] at hpL
        fin_cases hpL <;> omega
      have h1 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : 0 < p)
      have h2' : (p : ℚ) ≤ 23 := by exact_mod_cast hple.2
      rw [one_div]
      exact inv_anti₀ h1 h2'
    have hcards : B.card ≤ (L \ A).card := by
      have hLcard : L.card = 8 := by rw [hL]; decide
      have hAcard : A.card ≤ 8 := le_trans (Finset.card_filter_le _ _) hcard
      have hsd : (L \ A).card = L.card - A.card := Finset.card_sdiff_of_subset hAL
      have hAB : A.card + B.card = S.card := Finset.card_filter_add_card_filter_not _
      omega
    have hcast : (B.card : ℚ) ≤ ((L \ A).card : ℚ) := by exact_mod_cast hcards
    calc (B.card : ℚ) * (1 / 23) ≤ ((L \ A).card : ℚ) * (1 / 23) := by linarith
      _ = (L \ A).card • (1 / 23 : ℚ) := by simp [nsmul_eq_mul]
      _ ≤ ∑ p ∈ L \ A, (p : ℚ)⁻¹ := Finset.card_nsmul_le_sum _ _ _ hmem
  have hAeq : ∑ p ∈ A, (p : ℚ)⁻¹ = (∑ p ∈ L, (p : ℚ)⁻¹) - ∑ p ∈ L \ A, (p : ℚ)⁻¹ := by
    have h := Finset.sum_sdiff_eq_sub (f := fun p : ℕ => (p : ℚ)⁻¹) hAL
    linarith [h]
  have hLsum : ∑ p ∈ L, (p : ℚ)⁻¹ < 1 := by
    rw [hL]
    norm_num
  have hBnn : (0 : ℚ) ≤ (B.card : ℚ) := by positivity
  rw [hsplit, hAeq]
  linarith [hBbound, hLAbound, hLsum, hBnn]

/-- The prime factors of a Giuga number multiply back to it. -/
theorem IsGiuga.prod_primeFactors {n : ℕ} (h : IsGiuga n) : ∏ p ∈ n.primeFactors, p = n :=
  Nat.prod_primeFactors_of_squarefree h.squarefree

/-- The Giuga condition, restated with `n / p` written as a product over the other prime
factors of `n`. -/
theorem IsGiuga.dvd_prod_erase {n : ℕ} (h : IsGiuga n) (p : ℕ) (hpm : p ∈ n.primeFactors) :
    p ∣ (∏ q ∈ n.primeFactors.erase p, q) - 1 := by
  have hp : ∀ r ∈ n.primeFactors, r.Prime := fun r hrm => Nat.prime_of_mem_primeFactors hrm
  have hd := prod_div_eq_prod_erase hp p hpm
  rw [h.prod_primeFactors] at hd
  rw [← hd]
  exact h.2.2 p hpm

/-- A Giuga number has at least two distinct prime factors. -/
theorem IsGiuga.two_le_card {n : ℕ} (h : IsGiuga n) : 2 ≤ n.primeFactors.card := by
  have hprod := h.prod_primeFactors
  have hp : ∀ p ∈ n.primeFactors, p.Prime := fun p hpm => Nat.prime_of_mem_primeFactors hpm
  by_contra hlt
  push_neg at hlt
  interval_cases h' : n.primeFactors.card
  · have he : n.primeFactors = ∅ := Finset.card_eq_zero.1 h'
    rw [he] at hprod
    simp at hprod
    have := h.1
    omega
  · obtain ⟨p, hpe⟩ := Finset.card_eq_one.1 h'
    have hpp : p.Prime := hp p (by rw [hpe]; simp)
    rw [hpe] at hprod
    simp at hprod
    exact h.2.1 (hprod ▸ hpp)

/-- For a Giuga number, the sum of reciprocals of its prime factors exceeds `1`. -/
theorem IsGiuga.one_lt_sum_inv {n : ℕ} (h : IsGiuga n) :
    1 < ∑ p ∈ n.primeFactors, (p : ℚ)⁻¹ :=
  one_lt_sum_inv_of_dvd_prod_erase (fun _ hpm => Nat.prime_of_mem_primeFactors hpm)
    h.two_le_card h.dvd_prod_erase

/-- An odd Giuga number has at least nine distinct prime factors. -/
theorem odd_giuga_nine_le_card {n : ℕ} (hodd : Odd n) (h : IsGiuga n) :
    9 ≤ n.primeFactors.card := by
  by_contra hlt
  push_neg at hlt
  have hcard : n.primeFactors.card ≤ 8 := by omega
  have hp : ∀ p ∈ n.primeFactors, p.Prime := fun p hpm => Nat.prime_of_mem_primeFactors hpm
  have h2 : ∀ p ∈ n.primeFactors, p ≠ 2 := by
    intro p hpm hp2
    subst hp2
    have hd : (2 : ℕ) ∣ n := Nat.dvd_of_mem_primeFactors hpm
    rw [Nat.odd_iff] at hodd
    omega
  exact absurd h.one_lt_sum_inv (not_lt.2 (sum_inv_lt_one_of_odd_primes hp h2 hcard).le)

/-- An odd Giuga number is at least `3 ^ 9 = 19683`, since it is a product of at least nine
distinct odd primes. -/
theorem odd_giuga_ge {n : ℕ} (hodd : Odd n) (h : IsGiuga n) : 19683 ≤ n := by
  have hcard : 9 ≤ n.primeFactors.card := odd_giuga_nine_le_card hodd h
  have hprod : ∏ p ∈ n.primeFactors, p = n := h.prod_primeFactors
  have hge : ∀ p ∈ n.primeFactors, 3 ≤ p := by
    intro p hpm
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpm
    have hp2 : p ≠ 2 := by
      intro hp2
      subst hp2
      have hd : (2 : ℕ) ∣ n := Nat.dvd_of_mem_primeFactors hpm
      rw [Nat.odd_iff] at hodd
      omega
    have := hpp.two_le
    omega
  have hpow : 3 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
    calc 3 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 3 := by
          rw [Finset.prod_const]
      _ ≤ ∏ p ∈ n.primeFactors, p := Finset.prod_le_prod' hge
  have h39 : (3 : ℕ) ^ 9 ≤ 3 ^ n.primeFactors.card := Nat.pow_le_pow_right (by norm_num) hcard
  calc (19683 : ℕ) = 3 ^ 9 := by norm_num
    _ ≤ 3 ^ n.primeFactors.card := h39
    _ ≤ ∏ p ∈ n.primeFactors, p := hpow
    _ = n := hprod

/-- **Conditional existence of an odd Giuga number.**

Whether an odd Giuga number exists is an open problem.  This is a Lean-checked reduction:
if there is a finite set `S` of at least two odd primes such that every `p ∈ S`
divides `(∏ q ∈ S.erase p, q) - 1`, then `∏ p ∈ S, p` is an odd Giuga number, so an odd
Giuga number exists. -/
theorem OddGiugaExists {S : Finset ℕ} (hp : ∀ p ∈ S, p.Prime) (h2 : ∀ p ∈ S, p ≠ 2)
    (hcard : 2 ≤ S.card) (hdvd : ∀ p ∈ S, p ∣ (∏ q ∈ S.erase p, q) - 1) :
    ∃ n : ℕ, Odd n ∧ IsGiuga n := by
  classical
  obtain ⟨p₀, hp₀, q₀, hq₀, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
  set n : ℕ := ∏ p ∈ S, p with hn
  have hfac : n.primeFactors = S := by rw [hn]; exact Nat.primeFactors_prod hp
  have hsplit : p₀ * ∏ q ∈ S.erase p₀, q = n := Finset.mul_prod_erase S (fun q => q) hp₀
  have hq₀e : q₀ ∈ S.erase p₀ := Finset.mem_erase.2 ⟨Ne.symm hne, hq₀⟩
  have hXpos : 0 < ∏ q ∈ S.erase p₀, q :=
    Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2
      (fun q hq => (hp q (Finset.mem_of_mem_erase hq)).ne_zero))
  have hX2 : 2 ≤ ∏ q ∈ S.erase p₀, q := by
    have hdq : q₀ ∣ ∏ q ∈ S.erase p₀, q := Finset.dvd_prod_of_mem _ hq₀e
    have := Nat.le_of_dvd hXpos hdq
    have := (hp q₀ hq₀).two_le
    omega
  have hp₀2 : 2 ≤ p₀ := (hp p₀ hp₀).two_le
  have h1n : 1 < n := by
    rw [← hsplit]
    calc 1 < 2 * 2 := by norm_num
      _ ≤ p₀ * ∏ q ∈ S.erase p₀, q := Nat.mul_le_mul hp₀2 hX2
  refine ⟨n, ?_, h1n, ?_, ?_⟩
  · rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro hdvd2
    rw [hn] at hdvd2
    obtain ⟨q, hqS, hq2⟩ := (Prime.dvd_finset_prod_iff Nat.prime_two.prime _).1 hdvd2
    exact h2 q hqS (((Nat.prime_dvd_prime_iff_eq Nat.prime_two (hp q hqS)).1 hq2).symm)
  · rw [← hsplit]
    exact Nat.not_prime_mul (by omega) (by omega)
  · intro p hpm
    rw [hfac] at hpm
    rw [hn, prod_div_eq_prod_erase hp p hpm]
    exact hdvd p hpm

/-- The reduction used in `OddGiugaExists` is faithful: odd Giuga numbers correspond exactly
to finite sets `S` of at least two odd primes with `p ∣ (∏ q ∈ S.erase p, q) - 1` for all
`p ∈ S`. -/
theorem oddGiugaExists_iff :
    (∃ n : ℕ, Odd n ∧ IsGiuga n) ↔
      ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ (∀ p ∈ S, p ≠ 2) ∧ 2 ≤ S.card ∧
        ∀ p ∈ S, p ∣ (∏ q ∈ S.erase p, q) - 1 := by
  constructor
  · rintro ⟨n, hodd, h⟩
    refine ⟨n.primeFactors, fun p hpm => Nat.prime_of_mem_primeFactors hpm, ?_,
      h.two_le_card, h.dvd_prod_erase⟩
    intro p hpm hp2
    subst hp2
    have hd : (2 : ℕ) ∣ n := Nat.dvd_of_mem_primeFactors hpm
    rw [Nat.odd_iff] at hodd
    omega
  · rintro ⟨S, hp, h2, hcard, hdvd⟩
    exact OddGiugaExists hp h2 hcard hdvd

end Brockian.GiugaNumbers

