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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.SuperperfectNumbers

/-- A natural number `n` is *superperfect* if `σ (σ n) = 2 * n`, where `σ` is the
sum-of-divisors function. -/

theorem factorization_even_of_odd_sigma {n : ℕ} (hn : n ≠ 0) (hodd : Odd n) (h : Odd (σ 1 n))
    (p : ℕ) : Even (n.factorization p) := by
  by_contra hodde
  rw [Nat.not_even_iff_odd] at hodde
  have hp : p ∈ n.primeFactors := by
    by_contra hpm
    have h0 : n.factorization p = 0 := Finsupp.notMem_support_iff.mp (by
      simpa [Nat.support_factorization] using hpm)
    rw [h0] at hodde
    simp at hodde
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpodd : Odd p := by
    rcases hpp.eq_two_or_odd' with rfl | h2
    · exact absurd (Nat.dvd_of_mem_primeFactors hp) (by
        rintro h2
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2))
    · exact h2
  have hev : Even (∑ k ∈ Finset.range (n.factorization p + 1), p ^ k) := by
    rw [Finset.even_sum_iff_even_card_odd]
    have hfil : {x ∈ Finset.range (n.factorization p + 1) | Odd (p ^ x)}
        = Finset.range (n.factorization p + 1) :=
      Finset.filter_true_of_mem fun x _ => hpodd.pow
    rw [hfil, Finset.card_range]
    exact hodde.add_one
  have hdvd : (∑ k ∈ Finset.range (n.factorization p + 1), p ^ k) ∣ σ 1 n := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors hn]
    exact Finset.dvd_prod_of_mem _ hp
  exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hev).trans hdvd))) h

/-- An odd number with an odd sum of divisors is a perfect square. -/
