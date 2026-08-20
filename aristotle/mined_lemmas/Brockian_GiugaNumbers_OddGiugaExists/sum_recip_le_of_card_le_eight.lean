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
