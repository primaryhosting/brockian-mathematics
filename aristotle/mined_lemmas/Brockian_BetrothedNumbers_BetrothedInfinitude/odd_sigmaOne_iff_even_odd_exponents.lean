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

theorem odd_sigmaOne_iff_even_odd_exponents {n : ℕ} (hn : n ≠ 0) :
    Odd (sigmaOne n) ↔ ∀ p ∈ n.primeFactors, p ≠ 2 → Even (n.factorization p) := by
  rw [sigmaOne_eq_prod_factorization hn, ← Nat.not_even_iff_odd, even_iff_two_dvd,
    Finsupp.prod, Nat.support_factorization, Nat.prime_two.prime.dvd_finset_prod_iff]
  push_neg
  constructor
  · intro h p hp hp2
    have h2 := h p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd] at h2
    exact (odd_sigmaOne_prime_pow_iff hpp hp2).1 h2
  · intro h p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    by_cases hp2 : p = 2
    · subst hp2; exact odd_sigmaOne_two_pow _
    · exact (odd_sigmaOne_prime_pow_iff hpp hp2).2 (h p hp hp2)

/-- If `σ₁ n` is odd then `n` is a power of two times a square (equivalently, `n` is a
square or twice a square). -/
