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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean does not permit a `/-!` module docstring before `import`; the header above is the
-- same text as a plain block comment, and is repeated as a module docstring below.)
import Mathlib

/-!
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- A *betrothed* (quasi-amicable) pair: two distinct positive integers each of whose
sum of divisors equals `m + n + 1`. -/

theorem odd_sigma_iff {n : ℕ} (hn : n ≠ 0) :
    Odd (σ 1 n) ↔ ∀ p, p ≠ 2 → Even (n.factorization p) := by
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  simp only [mul_one]
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero, Prime.dvd_finset_prod_iff Nat.prime_two.prime]
  push_neg
  constructor
  · intro hall p hp
    by_cases hmem : p ∈ n.primeFactors
    · have hpp : p.Prime := Nat.prime_of_mem_primeFactors hmem
      have hodd : Odd p := hpp.odd_of_ne_two hp
      have h2 := hall p hmem
      rw [Nat.two_dvd_ne_zero, geom_sum_mod_two hodd] at h2
      rw [Nat.even_iff]; omega
    · have hz : n.factorization p = 0 := by
        rwa [← Finsupp.notMem_support_iff, Nat.support_factorization]
      simp [hz]
  · intro hall p hmem
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hmem
    by_cases hp : p = 2
    · subst hp
      rw [Nat.two_dvd_ne_zero, geom_sum_two_mod_two]
    · have hodd : Odd p := hpp.odd_of_ne_two hp
      rw [Nat.two_dvd_ne_zero, geom_sum_mod_two hodd]
      have h3 := hall p hp
      rw [Nat.even_iff] at h3; omega

/-- The sum of divisors of a number is odd exactly when it is a square or twice a square. -/
