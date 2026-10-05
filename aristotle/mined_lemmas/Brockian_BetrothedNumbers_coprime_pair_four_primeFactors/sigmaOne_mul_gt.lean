/-
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Note: the header is written as a plain block comment rather than a module docstring,
because Lean requires `import` commands to precede any docstring.)
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

/-- `sigmaOne n` is the sum of the divisors of `n`, i.e. `σ₁ n`. -/

lemma sigmaOne_mul_gt (m n : ℕ) (h : Betrothed m n) (hco : Nat.Coprime m n) :
    4 * (m * n) < sigmaOne (m * n) := by
  obtain ⟨hm, hn, -, hsm, hsn⟩ := h
  have hmul : sigmaOne (m * n) = sigmaOne m * sigmaOne n := by
    simpa [sigmaOne] using Nat.Coprime.sum_divisors_mul hco
  rw [hmul, hsm, hsn]
  zify
  nlinarith [sq_nonneg ((m : ℤ) - n), show (1:ℤ) ≤ m by exact_mod_cast hm,
    show (1:ℤ) ≤ n by exact_mod_cast hn]

/-- **Hagis–Lord, Proposition 2.** If `m` and `n` are coprime betrothed numbers, then `m * n`
has at least four distinct prime factors.

The proof combines multiplicativity of `σ` (giving `σ(mn) = (m+n+1)^2 > 4mn`) with the Euler
product bound `σ(N)/N ≤ ∏_{p ∣ N} p/(p-1)`: three or fewer distinct prime factors force
`∏ p/(p-1) ≤ 2 · (3/2) · (5/4) = 15/4 < 4`, a contradiction. -/
