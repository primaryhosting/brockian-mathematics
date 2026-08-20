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

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- `Betrothed m n` says that `(m, n)` is a betrothed (quasi-amicable) pair:
both are positive and `σ m = σ n = m + n + 1`. -/

lemma prod_primeRatio_le_prod_oddPrimesBelow :
    ∀ k : ℕ, k ≤ 20 → ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p ∧ p ≠ 2) → S.card ≤ k →
      ∏ p ∈ S, primeRatio p ≤ ∏ q ∈ oddPrimesBelow (bnd k), primeRatio q := by
  intro k
  induction k with
  | zero =>
      intro _ S _ hc
      have : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hc)
      subst this
      simp only [Finset.prod_empty]
      exact one_le_prod_primeRatio (fun q hq => one_le_primeRatio_of_mem hq)
  | succ k ih =>
      intro hk S hS hc
      have hk' : k < 20 := by omega
      by_cases hbig : ∃ p ∈ S, bnd k ≤ p
      · obtain ⟨p, hpS, hple⟩ := hbig
        have hcard : (S.erase p).card ≤ k := by
          have := Finset.card_erase_of_mem hpS
          omega
        have hIH := ih (by omega) (S.erase p) (fun q hq => hS q (Finset.mem_of_mem_erase hq)) hcard
        have hprod : ∏ q ∈ S, primeRatio q = primeRatio p * ∏ q ∈ S.erase p, primeRatio q :=
          (Finset.mul_prod_erase _ _ hpS).symm
        have hnotmem : bnd k ∉ oddPrimesBelow (bnd k) := by
          simp only [oddPrimesBelow, Finset.mem_filter, Finset.mem_range]
          omega
        have hstep : ∏ q ∈ oddPrimesBelow (bnd (k + 1)), primeRatio q
            = primeRatio (bnd k) * ∏ q ∈ oddPrimesBelow (bnd k), primeRatio q := by
          rw [oddPrimesBelow_succ hk', Finset.prod_insert hnotmem]
        rw [hprod, hstep]
        have h1 : primeRatio p ≤ primeRatio (bnd k) :=
          primeRatio_le_of_le (two_le_bnd (by omega)) hple
        have h2 : (0 : ℚ) ≤ ∏ q ∈ S.erase p, primeRatio q :=
          Finset.prod_nonneg (fun q hq => primeRatio_nonneg (hS q (Finset.mem_of_mem_erase hq)).1.two_le)
        have h3 : (0 : ℚ) ≤ primeRatio (bnd k) := primeRatio_nonneg (two_le_bnd (by omega))
        exact mul_le_mul h1 hIH h2 h3
      · push_neg at hbig
        have hsub : S ⊆ oddPrimesBelow (bnd (k + 1)) := by
          intro p hp
          have hlt : p < bnd k := hbig p hp
          have := oddPrimesBelow_mono (bnd_le_succ hk')
          apply this
          simp only [oddPrimesBelow, Finset.mem_filter, Finset.mem_range]
          exact ⟨hlt, (hS p hp).1, (hS p hp).2⟩
        exact prod_primeRatio_le_of_subset hsub (fun q hq => one_le_primeRatio_of_mem hq)

/-- The twenty smallest odd primes. -/
