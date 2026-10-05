/-
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Finset

/-! ## Basic definitions -/

/-- `sigmaOne n` is the sum-of-divisors function `σ₁(n) = ∑_{d ∣ n} d`. -/

lemma coprime_isSquare_mul_iff {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) :
    IsSquare (a * b) ↔ IsSquare a ∧ IsSquare b := by
  rw [isSquare_iff_factorization_even (Nat.mul_ne_zero ha hb),
    isSquare_iff_factorization_even ha, isSquare_iff_factorization_even hb,
    Nat.factorization_mul ha hb]
  constructor
  · intro h
    have hdisj : Disjoint a.primeFactors b.primeFactors := hab.disjoint_primeFactors
    constructor <;> intro p <;> have hp := h p <;> simp only [Finsupp.add_apply] at hp
    · by_cases h0 : a.factorization p = 0
      · simp [h0]
      · have hmem : p ∈ a.primeFactors := by
          rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.mpr h0
        have hnot : p ∉ b.primeFactors := Finset.disjoint_left.mp hdisj hmem
        have h1 : b.factorization p = 0 := by
          rw [← Nat.support_factorization] at hnot
          exact Finsupp.notMem_support_iff.mp hnot
        rwa [h1, add_zero] at hp
    · by_cases h0 : b.factorization p = 0
      · simp [h0]
      · have hmem : p ∈ b.primeFactors := by
          rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.mpr h0
        have hnot : p ∉ a.primeFactors := Finset.disjoint_right.mp hdisj hmem
        have h1 : a.factorization p = 0 := by
          rw [← Nat.support_factorization] at hnot
          exact Finsupp.notMem_support_iff.mp hnot
        rwa [h1, zero_add] at hp
  · rintro ⟨h1, h2⟩ p
    simpa using (h1 p).add (h2 p)

/-- For a positive odd `n`, the divisor sum `σ₁(n)` is odd exactly when `n` is a perfect
square. -/
