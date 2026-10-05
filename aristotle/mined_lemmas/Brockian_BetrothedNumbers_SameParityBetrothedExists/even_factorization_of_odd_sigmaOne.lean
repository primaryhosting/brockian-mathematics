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

import Mathlib

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset

/-- `sigmaOne n` is the sum of all divisors of `n`. -/

lemma even_factorization_of_odd_sigmaOne {n : ℕ} (hn : n ≠ 0) (h : Odd (sigmaOne n))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : Even (n.factorization p) := by
  by_cases hmem : p ∈ n.factorization.support
  · have hprod := (isMultiplicative_sigma (k := 1)).multiplicative_factorization _ hn
    have hdvd : (sigma 1) (p ^ n.factorization p) ∣ (sigma 1) n := by
      rw [hprod]
      exact Finset.dvd_prod_of_mem (fun q => (sigma 1) (q ^ n.factorization q)) hmem
    rw [← sigmaOne_eq_sigma, ← sigmaOne_eq_sigma] at hdvd
    refine (odd_sigmaOne_prime_pow_iff hp hp2 _).mp ?_
    rcases Nat.even_or_odd (sigmaOne (p ^ n.factorization p)) with he | ho
    · exfalso
      have h2 : 2 ∣ sigmaOne n := dvd_trans he.two_dvd hdvd
      have := Nat.odd_iff.mp h
      omega
    · exact ho
  · simp [Finsupp.notMem_support_iff.mp hmem]

/-- If `σ(n)` is odd then `n` is a square or twice a square. -/
