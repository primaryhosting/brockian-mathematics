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

lemma geom_sum_mul_pred_le (p a : ℕ) (hp : 1 ≤ p) :
    (∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1) ≤ p ^ (a + 1) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, add_mul]
    calc (∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1) + p ^ (a + 1) * (p - 1)
        ≤ p ^ (a + 1) + p ^ (a + 1) * (p - 1) := by gcongr
      _ = p ^ (a + 1) * (1 + (p - 1)) := by ring
      _ = p ^ (a + 1 + 1) := by rw [show 1 + (p - 1) = p from by omega]; ring

/-- The abundancy bound coming from the Euler product:
`σ(N) * ∏_{p ∣ N} (p - 1) ≤ N * ∏_{p ∣ N} p`, i.e. `σ(N)/N ≤ ∏_{p ∣ N} p/(p-1)`. -/
