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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-!` module docstring:
-- Lean 4 requires `import` commands to precede every other command, including module
-- docstrings.  The same text is repeated as the module docstring after the import.)

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 40000

set_option maxHeartbeats 2000000

namespace Brockian.BetrothedNumbers

open Finset

/-- The classical divisor sum `σ₁ n = ∑_{d ∣ n} d`. -/

theorem eq_two_pow_mul_sq_of_odd_sigmaOne {n : ℕ} (hn : n ≠ 0) (h : Odd (sigmaOne n)) :
    ∃ a k : ℕ, 0 < k ∧ n = 2 ^ a * k ^ 2 := by
  classical
  have hall := (odd_sigmaOne_iff_even_odd_exponents hn).1 h
  refine ⟨n.factorization 2, ∏ p ∈ n.primeFactors.erase 2, p ^ (n.factorization p / 2), ?_, ?_⟩
  · exact Finset.prod_pos fun p hp =>
      pow_pos (Nat.pos_of_mem_primeFactors (Finset.mem_of_mem_erase hp)) _
  · have hprod : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
      simpa [Finsupp.prod, Nat.support_factorization] using Nat.factorization_prod_pow_eq_self hn
    have hsq : (∏ p ∈ n.primeFactors.erase 2, p ^ (n.factorization p / 2)) ^ 2
        = ∏ p ∈ n.primeFactors.erase 2, p ^ n.factorization p := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun p hp => ?_
      have he : Even (n.factorization p) :=
        hall p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp)
      rw [← pow_mul]
      obtain ⟨t, ht⟩ := he
      congr 1
      omega
    rw [hsq]
    by_cases h2 : 2 ∈ n.primeFactors
    · rw [← Finset.mul_prod_erase _ _ h2] at hprod
      exact hprod.symm
    · have hz : n.factorization 2 = 0 := by
        simpa [Nat.support_factorization] using
          (Nat.factorization n).notMem_support_iff.1 (by simpa [Nat.support_factorization] using h2)
      rw [hz, Finset.erase_eq_of_notMem h2, hprod, pow_zero, one_mul]

/-- **Parity structure of betrothed pairs.**  If the two members of a betrothed pair have the
same parity, then each of them is a power of two times a square (i.e. a square or twice a
square).  In particular a betrothed pair whose members are not of this shape must consist of
one even and one odd number, as is the case for all pairs known. -/
