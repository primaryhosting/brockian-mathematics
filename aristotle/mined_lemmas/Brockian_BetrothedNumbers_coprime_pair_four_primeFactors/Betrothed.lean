import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction Finset

/-- `Betrothed m n` says that `m` and `n` are *betrothed* (quasi-amicable) numbers:
both are positive and each one's sum of divisors equals `m + n + 1`. -/

def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ (sigma 1) m = m + n + 1 ∧ (sigma 1) n = m + n + 1

/-- Sanity check that the definition is non-degenerate: `(48, 75)` is the smallest
betrothed pair (`σ 48 = σ 75 = 124 = 48 + 75 + 1`).  It is not coprime. -/
example : Betrothed 48 75 := ⟨by norm_num, by norm_num, by decide, by decide⟩

/-- Geometric sum identity: `(1 + p + ⋯ + p ^ k) * (p - 1) + 1 = p ^ (k + 1)` for `p ≥ 1`. -/
