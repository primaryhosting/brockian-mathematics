/-
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
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

set_option grind.warning false

/-!
## Betrothed (quasi-amicable) numbers

A pair `(m, n)` of positive integers is *betrothed* (or *quasi-amicable*) when each of the two
numbers is the sum of the **non-trivial** divisors of the other, i.e.

`σ(m) = σ(n) = m + n + 1`.

This file formalizes the second half of Proposition 2 of Hagis and Lord, *Quasi-amicable numbers*
(Math. Comp. 31 (1977)): if the two members of a betrothed pair are **coprime** and have the
**same parity**, then both are odd (indeed both are perfect squares) and the product `m * n` has
at least twenty-one distinct prime factors.

The proof is completely elementary:

* both members are odd, since two coprime numbers cannot both be even;
* therefore `σ(m) = m + n + 1` is odd, so `m` (and likewise `n`) is a perfect square, by
  `Brockian.BetrothedNumbers.odd_sigma_one_iff`;
* by coprimality `σ(mn) = σ(m)σ(n) = (m + n + 1)^2 > 4mn`, so the odd number `N = mn` has
  abundancy `σ(N)/N > 4`;
* the abundancy of `N` is bounded above by `∏_{p ∣ N} p/(p-1)`, and the product of `p/(p-1)`
  over any twenty distinct odd primes is at most the value taken over the twenty smallest odd
  primes `3, 5, …, 73`, which is `< 4`.

Hence `ω(mn) ≥ 21`. This bound is exactly what is proved here; it is a *theorem*, and should be
distinguished from the (much larger) **computational** lower bounds that appear in the
literature, which rest on extensive machine search rather than on proof. Such historical
numerical records — e.g. that no coprime betrothed pair of the same parity is known at all, and
that searches have ruled out all such pairs below various large bounds — are deliberately **not**
stated as Lean theorems anywhere in this file; only the unconditional inequality `21 ≤ ω(mn)` is.
-/

namespace Brockian.BetrothedNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- A *betrothed* (quasi-amicable) pair: `σ m = σ n = m + n + 1`, i.e. each number is the sum of
the non-trivial divisors (excluding `1` and the number itself) of the other. -/

lemma prod_primeMult_le_aux (k : ℕ) : ∀ S : Finset ℕ, (S \ oddPrimes20).card = k →
    (∀ p ∈ S, p.Prime ∧ p ≠ 2) → S.card ≤ 20 →
    ∏ p ∈ S, primeMult p ≤ ∏ p ∈ oddPrimes20, primeMult p := by
  induction k with
  | zero =>
      intro S hk hS _
      have hsub : S ⊆ oddPrimes20 := by
        rwa [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hk
      rw [← Finset.prod_sdiff hsub]
      have h1 : (1:ℚ) ≤ ∏ p ∈ oddPrimes20 \ S, primeMult p :=
        one_le_prod_primeMult (fun i hi => (oddPrimes20_spec (Finset.mem_sdiff.mp hi).1).1.two_le)
      have h2 : (0:ℚ) < ∏ p ∈ S, primeMult p :=
        Finset.prod_pos (fun i hi => primeMult_pos (hS i hi).1.two_le)
      nlinarith
  | succ k ih =>
      intro S hk hS hcard
      have hne : (S \ oddPrimes20).Nonempty := by
        rw [← Finset.card_pos, hk]; omega
      obtain ⟨p, hpmem⟩ := hne
      have hpS : p ∈ S := (Finset.mem_sdiff.mp hpmem).1
      have hpP : p ∉ oddPrimes20 := (Finset.mem_sdiff.mp hpmem).2
      have hp73 : 73 < p := by
        by_contra hcon
        exact hpP (mem_oddPrimes20 (hS p hpS).1 (hS p hpS).2 (by omega))
      have hc1 : (S \ oddPrimes20).card + (S ∩ oddPrimes20).card = S.card :=
        Finset.card_sdiff_add_card_inter S oddPrimes20
      have hc2 : (oddPrimes20 \ S).card + (oddPrimes20 ∩ S).card = oddPrimes20.card :=
        Finset.card_sdiff_add_card_inter oddPrimes20 S
      have hc3 : (oddPrimes20 ∩ S).card = (S ∩ oddPrimes20).card := by rw [Finset.inter_comm]
      have hc4 : oddPrimes20.card = 20 := by decide
      have hqne : (oddPrimes20 \ S).Nonempty := by rw [← Finset.card_pos]; omega
      obtain ⟨q, hqmem⟩ := hqne
      have hqP : q ∈ oddPrimes20 := (Finset.mem_sdiff.mp hqmem).1
      have hqS : q ∉ S := (Finset.mem_sdiff.mp hqmem).2
      obtain ⟨hqprime, hq2, hq73⟩ := oddPrimes20_spec hqP
      set T := S.erase p with hT
      have hqT : q ∉ T := fun h => hqS (Finset.mem_of_mem_erase h)
      have hS' : ∀ x ∈ insert q T, x.Prime ∧ x ≠ 2 := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ⟨hqprime, hq2⟩
        · exact hS x (Finset.mem_of_mem_erase hx)
      have hcardT : T.card + 1 = S.card := by
        rw [hT, Finset.card_erase_of_mem hpS]
        have : 1 ≤ S.card := Finset.card_pos.mpr ⟨p, hpS⟩
        omega
      have hcard' : (insert q T).card ≤ 20 := by
        rw [Finset.card_insert_of_notMem hqT]; omega
      have hsd : ((insert q T) \ oddPrimes20).card = k := by
        rw [Finset.insert_sdiff_of_mem _ hqP]
        have hTP : T \ oddPrimes20 = (S \ oddPrimes20).erase p := by
          rw [hT, Finset.erase_sdiff_comm]
        rw [hTP, Finset.card_erase_of_mem hpmem, hk]
        omega
      have hIH := ih (insert q T) hsd hS' hcard'
      have hprodT : (0:ℚ) < ∏ x ∈ T, primeMult x :=
        Finset.prod_pos (fun i hi => primeMult_pos (hS i (Finset.mem_of_mem_erase hi)).1.two_le)
      have h1 : ∏ x ∈ S, primeMult x = primeMult p * ∏ x ∈ T, primeMult x := by
        rw [hT, Finset.mul_prod_erase _ _ hpS]
      have h2 : ∏ x ∈ insert q T, primeMult x = primeMult q * ∏ x ∈ T, primeMult x :=
        Finset.prod_insert hqT
      have hle : primeMult p ≤ primeMult q := primeMult_anti hqprime.two_le (by omega)
      rw [h1]
      rw [h2] at hIH
      nlinarith

/-- Over any at most twenty distinct odd primes, `∏ p/(p-1)` is maximal for the twenty
smallest odd primes. -/
