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
# Odd Giuga numbers

A *Giuga number* is a composite `n` such that `p ∣ n / p - 1` for every prime `p ∣ n`.
The smallest one is `30`; whether an **odd** Giuga number exists is an open problem.

Accordingly the target `Brockian.GiugaNumbers.OddGiugaExists` is stated and proved here as
a Lean-checked *reduction*: an odd Giuga number exists if and only if there is a finite set
`S` of at least two odd primes such that `p ∣ (∏_{q ∈ S, q ≠ p} q) - 1` for every `p ∈ S`
(`GiugaSet S`). This converts the question into a search over finite sets of odd primes.

Along the way we prove, unconditionally:

* `IsGiuga.squarefree` — every Giuga number is squarefree;
* `isGiuga_thirty` — `30` is a Giuga number;
* `IsGiuga.giugaSet_primeFactors` / `GiugaSet.isGiuga_prod` — the two halves of the reduction;
* `GiugaSet.one_lt_sum_recip` — for a Giuga set `S` one has `∑_{p ∈ S} 1/p > 1`;
* `GiugaSet.nine_le_card` and `IsGiuga.nine_le_card_primeFactors` — consequently an odd
  Giuga number has at least nine distinct prime factors.
-/

namespace Brockian.GiugaNumbers

open Finset

/-- A *Giuga number* is a composite natural number `n` such that every prime `p`
dividing `n` satisfies `p ∣ n / p - 1`. -/
def IsGiuga (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ∣ (n / p - 1)

/-- Sanity check: `30 = 2 * 3 * 5` is the smallest Giuga number. -/
theorem isGiuga_thirty : IsGiuga 30 := by
  refine ⟨by norm_num, by decide, ?_⟩
  intro p hp hpd
  have hple : p ≤ 30 := Nat.le_of_dvd (by norm_num) hpd
  interval_cases p <;> revert hp hpd <;> decide

/-- Every Giuga number is squarefree. -/
theorem IsGiuga.squarefree {n : ℕ} (h : IsGiuga n) : Squarefree n := by
  obtain ⟨hn1, -, hdvd⟩ := h
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpn : p ∣ n := dvd_trans (Dvd.intro p rfl) hpp
  have h1 : p ∣ n / p := by
    obtain ⟨k, hk⟩ := hpp
    exact ⟨k, by rw [hk, Nat.mul_assoc, Nat.mul_div_cancel_left _ hp.pos]⟩
  have hq : 1 ≤ n / p := (Nat.one_le_div_iff hp.pos).2 (Nat.le_of_dvd (by omega) hpn)
  have h2 : p ∣ (n / p) - (n / p - 1) := Nat.dvd_sub h1 (hdvd p hp hpn)
  have he : (n / p) - (n / p - 1) = 1 := by omega
  rw [he] at h2
  exact hp.one_lt.ne' (Nat.dvd_one.1 h2)

/-- The criterion, on a finite set `S` of primes, for `∏ S` to be an odd Giuga number:
`S` consists of at least two odd primes, and each `p ∈ S` divides `(∏_{q ∈ S, q ≠ p} q) - 1`. -/
def GiugaSet (S : Finset ℕ) : Prop :=
  2 ≤ S.card ∧ (∀ p ∈ S, p.Prime) ∧ (∀ p ∈ S, Odd p) ∧
    ∀ p ∈ S, p ∣ (∏ q ∈ S.erase p, q) - 1

/-- A prime dividing a product of primes over a finset belongs to that finset. -/
theorem mem_of_prime_dvd_prod {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p : ℕ}
    (hp : p.Prime) (hd : p ∣ ∏ q ∈ S, q) : p ∈ S := by
  obtain ⟨q, hqS, hpq⟩ := (Nat.Prime.prime hp).exists_mem_finset_dvd hd
  rwa [(Nat.prime_dvd_prime_iff_eq hp (hS q hqS)).1 hpq]

/-- A product of primes over a finset is positive. -/
theorem prod_primes_pos {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) : 0 < ∏ q ∈ S, q :=
  Finset.prod_pos fun q hq => (hS q hq).pos

/-- If `S` is a nonempty finset of primes then `2 ≤ ∏ S`. -/
theorem two_le_prod_primes {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) (hne : S.Nonempty) :
    2 ≤ ∏ q ∈ S, q := by
  obtain ⟨q, hq⟩ := hne
  exact le_trans (hS q hq).two_le
    (Nat.le_of_dvd (prod_primes_pos hS) (Finset.dvd_prod_of_mem _ hq))

/-! ### The two halves of the reduction -/

/-- If `n` is an odd Giuga number then its set of prime factors is a Giuga set. -/
theorem IsGiuga.giugaSet_primeFactors {n : ℕ} (hodd : Odd n) (h : IsGiuga n) :
    GiugaSet n.primeFactors := by
  obtain ⟨hn1, hnp, hdvd⟩ := h
  have hsq : Squarefree n := IsGiuga.squarefree ⟨hn1, hnp, hdvd⟩
  have hprod : ∏ p ∈ n.primeFactors, p = n := Nat.prod_primeFactors_of_squarefree hsq
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 hn1
  refine ⟨?_, fun p hp => Nat.prime_of_mem_primeFactors hp, ?_, ?_⟩
  · by_contra hcard
    push_neg at hcard
    have h1 : n.primeFactors.card = 1 := by
      have := Finset.card_pos.2 hne
      omega
    obtain ⟨p, hp⟩ := Finset.card_eq_one.1 h1
    rw [hp, Finset.prod_singleton] at hprod
    have hmem : p ∈ n.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
    exact hnp (hprod ▸ Nat.prime_of_mem_primeFactors hmem)
  · intro p hp
    refine (Nat.prime_of_mem_primeFactors hp).odd_of_ne_two ?_
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd)
      (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hmul : n = (∏ q ∈ n.primeFactors.erase p, q) * p := by
      rw [mul_comm, Finset.mul_prod_erase _ (fun q => q) hp, hprod]
    have hdiv : n / p = ∏ q ∈ n.primeFactors.erase p, q :=
      Nat.div_eq_of_eq_mul_left hpp.pos hmul
    rw [← hdiv]
    exact hdvd p hpp (Nat.dvd_of_mem_primeFactors hp)

/-- The product of a Giuga set is an odd Giuga number. -/
theorem GiugaSet.isGiuga_prod {S : Finset ℕ} (h : GiugaSet S) :
    Odd (∏ q ∈ S, q) ∧ IsGiuga (∏ q ∈ S, q) := by
  obtain ⟨hcard, hprime, hodd, hdvd⟩ := h
  have hne : S.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨p, hpS⟩ := hne
  have hpp := hprime p hpS
  have hmul : p * ∏ q ∈ S.erase p, q = ∏ q ∈ S, q :=
    Finset.mul_prod_erase _ (fun q => q) hpS
  have herase : (S.erase p).Nonempty := by
    refine Finset.card_pos.1 ?_
    rw [Finset.card_erase_of_mem hpS]
    omega
  have hm2 : 2 ≤ ∏ q ∈ S.erase p, q :=
    two_le_prod_primes (fun q hq => hprime q (Finset.mem_of_mem_erase hq)) herase
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Nat.odd_iff, ← Nat.not_even_iff, even_iff_two_dvd]
    intro h2
    have h2S := mem_of_prime_dvd_prod hprime Nat.prime_two h2
    have := hodd 2 h2S
    rw [Nat.odd_iff] at this
    omega
  · rw [← hmul]
    calc 1 < 2 * 2 := by norm_num
      _ ≤ p * ∏ q ∈ S.erase p, q := Nat.mul_le_mul hpp.two_le hm2
  · rw [← hmul]
    exact Nat.not_prime_mul hpp.one_lt.ne' (by omega)
  · intro r hr hrd
    have hrS : r ∈ S := mem_of_prime_dvd_prod hprime hr hrd
    have hmulr : (∏ q ∈ S, q) = (∏ q ∈ S.erase r, q) * r := by
      rw [mul_comm]; exact (Finset.mul_prod_erase _ (fun q => q) hrS).symm
    have hdivr : (∏ q ∈ S, q) / r = ∏ q ∈ S.erase r, q :=
      Nat.div_eq_of_eq_mul_left hr.pos hmulr
    rw [hdivr]
    exact hdvd r hrS

/-- **Reduction of the existence of an odd Giuga number to a search over finite sets of
odd primes.** There is an odd Giuga number if and only if there is a finite set `S` of at
least two odd primes such that each `p ∈ S` divides `(∏_{q ∈ S, q ≠ p} q) - 1`.

Whether an odd Giuga number exists is an open problem; this theorem is a Lean-checked
equivalence (a reduction), not a resolution of it. -/
theorem OddGiugaExists :
    (∃ n : ℕ, Odd n ∧ IsGiuga n) ↔ (∃ S : Finset ℕ, GiugaSet S) := by
  constructor
  · rintro ⟨n, hodd, hG⟩
    exact ⟨n.primeFactors, hG.giugaSet_primeFactors hodd⟩
  · rintro ⟨S, hS⟩
    exact ⟨∏ q ∈ S, q, hS.isGiuga_prod⟩

/-! ### An odd Giuga number has at least nine prime factors -/

/-- For a Giuga set `S`, the product `∏ S` divides `(∑_{r ∈ S} ∏_{q ∈ S, q ≠ r} q) - 1`. -/
theorem GiugaSet.prod_dvd_sum_sub_one {S : Finset ℕ} (h : GiugaSet S) :
    (∏ q ∈ S, q) ∣ (∑ r ∈ S, ∏ q ∈ S.erase r, q) - 1 := by
  obtain ⟨-, hprime, -, hdvd⟩ := h
  refine Finset.prod_primes_dvd _ (fun p hp => (hprime p hp).prime) ?_
  intro p hpS
  have hsplit : (∏ q ∈ S.erase p, q) + ∑ r ∈ S.erase p, ∏ q ∈ S.erase r, q
      = ∑ r ∈ S, ∏ q ∈ S.erase r, q :=
    Finset.add_sum_erase S (fun r => ∏ q ∈ S.erase r, q) hpS
  have hA1 : 1 ≤ ∏ q ∈ S.erase p, q :=
    prod_primes_pos (fun q hq => hprime q (Finset.mem_of_mem_erase hq))
  have hB : p ∣ ∑ r ∈ S.erase p, ∏ q ∈ S.erase r, q := by
    refine Finset.dvd_sum ?_
    intro r hr
    refine Finset.dvd_prod_of_mem _ ?_
    exact Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase hr).symm, hpS⟩
  have hrw : (∑ r ∈ S, ∏ q ∈ S.erase r, q) - 1
      = ((∏ q ∈ S.erase p, q) - 1) + ∑ r ∈ S.erase p, ∏ q ∈ S.erase r, q := by
    rw [← hsplit]; omega
  rw [hrw]
  exact Nat.dvd_add (hdvd p hpS) hB

/-- For a Giuga set `S`, the reciprocals of its elements sum to more than `1`. -/
theorem GiugaSet.one_lt_sum_recip {S : Finset ℕ} (h : GiugaSet S) :
    1 < ∑ p ∈ S, (1 : ℚ) / p := by
  obtain ⟨hcard, hprime, hodd, hdvd⟩ := h
  have hne : S.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨p₀, hp₀⟩ := hne
  set n : ℕ := ∏ q ∈ S, q with hn
  set M : ℕ := ∑ r ∈ S, ∏ q ∈ S.erase r, q with hM
  have hnpos : 0 < n := prod_primes_pos hprime
  have herase : (S.erase p₀).Nonempty := by
    refine Finset.card_pos.1 ?_
    rw [Finset.card_erase_of_mem hp₀]
    omega
  have hterm : 2 ≤ ∏ q ∈ S.erase p₀, q :=
    two_le_prod_primes (fun q hq => hprime q (Finset.mem_of_mem_erase hq)) herase
  have hM2 : 2 ≤ M := by
    refine le_trans hterm ?_
    exact Finset.single_le_sum (f := fun r => ∏ q ∈ S.erase r, q) (fun i _ => Nat.zero_le _) hp₀
  have hdvd' : n ∣ M - 1 := GiugaSet.prod_dvd_sum_sub_one ⟨hcard, hprime, hodd, hdvd⟩
  have hle : n ≤ M - 1 := Nat.le_of_dvd (by omega) hdvd'
  have hltQ : (n : ℚ) < (M : ℚ) := by
    have : n < M := by omega
    exact_mod_cast this
  have hMQ : (M : ℚ) = (n : ℚ) * ∑ p ∈ S, (1 : ℚ) / p := by
    rw [Finset.mul_sum, hM]
    push_cast
    refine Finset.sum_congr rfl ?_
    intro r hr
    have hmulr : (∏ q ∈ S, q) = (∏ q ∈ S.erase r, q) * r := by
      rw [mul_comm]; exact (Finset.mul_prod_erase _ (fun q => q) hr).symm
    have hrne : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (hprime r hr).pos.ne'
    field_simp
    rw [hn, ← Nat.cast_prod]
    exact_mod_cast hmulr.symm
  rw [hMQ] at hltQ
  have hnQ : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hnpos
  nlinarith [hltQ, hnQ]

/-- The eight smallest odd primes. -/
def smallOddPrimes : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 23}

theorem card_smallOddPrimes : smallOddPrimes.card = 8 := by decide

theorem sum_recip_smallOddPrimes_lt_one : ∑ p ∈ smallOddPrimes, (1 : ℚ) / p < 1 := by
  norm_num [smallOddPrimes]

theorem twentynine_le_of_odd_prime_not_mem {x : ℕ} (hp : x.Prime) (ho : Odd x)
    (hT : x ∉ smallOddPrimes) : 29 ≤ x := by
  by_contra hlt
  push_neg at hlt
  interval_cases x <;> revert hp ho hT <;> decide

theorem prime_of_mem_smallOddPrimes {y : ℕ} (hy : y ∈ smallOddPrimes) : y.Prime ∧ Odd y := by
  revert hy
  simp only [smallOddPrimes, Finset.mem_insert, Finset.mem_singleton]
  rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    exact ⟨by norm_num, by decide⟩

theorem le_of_mem_smallOddPrimes {y : ℕ} (hy : y ∈ smallOddPrimes) : y ≤ 23 := by
  revert hy
  simp only [smallOddPrimes, Finset.mem_insert, Finset.mem_singleton]
  rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> norm_num

/-- Among finite sets of at most eight odd primes, the eight smallest odd primes maximise
the sum of reciprocals.  (Proved by an exchange argument, by induction on the number of
elements outside `smallOddPrimes`.) -/
theorem sum_recip_le_of_card_le_eight :
    ∀ (m : ℕ) (S : Finset ℕ), (S \ smallOddPrimes).card = m → (∀ p ∈ S, p.Prime) →
      (∀ p ∈ S, Odd p) → S.card ≤ 8 →
      ∑ p ∈ S, (1 : ℚ) / p ≤ ∑ p ∈ smallOddPrimes, (1 : ℚ) / p := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro S hm hp ho hc
    rcases Finset.eq_empty_or_nonempty (S \ smallOddPrimes) with hd | hd
    · rw [Finset.sdiff_eq_empty_iff_subset] at hd
      exact Finset.sum_le_sum_of_subset_of_nonneg hd (fun i _ _ => by positivity)
    · obtain ⟨x, hx⟩ := hd
      rw [Finset.mem_sdiff] at hx
      obtain ⟨hxS, hxT⟩ := hx
      have hx29 : 29 ≤ x := twentynine_le_of_odd_prime_not_mem (hp x hxS) (ho x hxS) hxT
      have hTS : (smallOddPrimes \ S).Nonempty := by
        rw [Finset.sdiff_nonempty]
        intro hsub
        have hins : insert x smallOddPrimes ⊆ S := Finset.insert_subset hxS hsub
        have := Finset.card_le_card hins
        rw [Finset.card_insert_of_notMem hxT, card_smallOddPrimes] at this
        omega
      obtain ⟨y, hy⟩ := hTS
      rw [Finset.mem_sdiff] at hy
      obtain ⟨hyT, hyS⟩ := hy
      have hy23 : y ≤ 23 := le_of_mem_smallOddPrimes hyT
      have hy3 := prime_of_mem_smallOddPrimes hyT
      have hynem : y ∉ S.erase x := fun hmem => hyS (Finset.mem_of_mem_erase hmem)
      set S' : Finset ℕ := insert y (S.erase x) with hS'
      -- the new set has the same cardinality
      have hcard' : S'.card = S.card := by
        rw [hS', Finset.card_insert_of_notMem hynem, Finset.card_erase_of_mem hxS]
        have : 1 ≤ S.card := Finset.card_pos.2 ⟨x, hxS⟩
        omega
      -- the new set consists of odd primes
      have hp' : ∀ p ∈ S', p.Prime := by
        intro q hq
        rcases Finset.mem_insert.1 hq with rfl | hq
        · exact hy3.1
        · exact hp q (Finset.mem_of_mem_erase hq)
      have ho' : ∀ p ∈ S', Odd p := by
        intro q hq
        rcases Finset.mem_insert.1 hq with rfl | hq
        · exact hy3.2
        · exact ho q (Finset.mem_of_mem_erase hq)
      -- its difference with `smallOddPrimes` is strictly smaller
      have hdiff : S' \ smallOddPrimes = (S \ smallOddPrimes).erase x := by
        rw [hS', Finset.insert_sdiff_of_mem _ hyT]
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        tauto
      have hlt : (S' \ smallOddPrimes).card < m := by
        rw [hdiff, Finset.card_erase_of_mem (Finset.mem_sdiff.2 ⟨hxS, hxT⟩), hm]
        have : 1 ≤ m := by
          rw [← hm]
          exact Finset.card_pos.2 ⟨x, Finset.mem_sdiff.2 ⟨hxS, hxT⟩⟩
        omega
      -- the sum can only increase
      have hxpos : (0 : ℚ) < (x : ℚ) := by
        have : (29 : ℚ) ≤ (x : ℚ) := by exact_mod_cast hx29
        linarith
      have hypos : (0 : ℚ) < (y : ℚ) := by
        have := hy3.1.pos
        exact_mod_cast this
      have hyx : (y : ℚ) ≤ (x : ℚ) := by
        have h1 : (y : ℚ) ≤ 23 := by exact_mod_cast hy23
        have h2 : (29 : ℚ) ≤ (x : ℚ) := by exact_mod_cast hx29
        linarith
      have hsumS : (1 : ℚ) / x + ∑ q ∈ S.erase x, (1 : ℚ) / q = ∑ q ∈ S, (1 : ℚ) / q :=
        Finset.add_sum_erase S (fun q => (1 : ℚ) / q) hxS
      have hsumS' : ∑ q ∈ S', (1 : ℚ) / q = (1 : ℚ) / y + ∑ q ∈ S.erase x, (1 : ℚ) / q := by
        rw [hS', Finset.sum_insert hynem]
      have hmono : ∑ q ∈ S, (1 : ℚ) / q ≤ ∑ q ∈ S', (1 : ℚ) / q := by
        rw [← hsumS, hsumS']
        have : (1 : ℚ) / x ≤ (1 : ℚ) / y := one_div_le_one_div_of_le hypos hyx
        linarith
      exact le_trans hmono
        (ih _ hlt S' rfl hp' ho' (by omega))

/-- A Giuga set has at least nine elements. -/
theorem GiugaSet.nine_le_card {S : Finset ℕ} (h : GiugaSet S) : 9 ≤ S.card := by
  by_contra hlt
  push_neg at hlt
  have h1 := h.one_lt_sum_recip
  have h2 := sum_recip_le_of_card_le_eight (S \ smallOddPrimes).card S rfl h.2.1 h.2.2.1
    (by omega)
  have h3 := sum_recip_smallOddPrimes_lt_one
  linarith

/-- An odd Giuga number has at least nine distinct prime factors. -/
theorem IsGiuga.nine_le_card_primeFactors {n : ℕ} (hodd : Odd n) (h : IsGiuga n) :
    9 ≤ n.primeFactors.card :=
  GiugaSet.nine_le_card (h.giugaSet_primeFactors hodd)

end Brockian.GiugaNumbers

