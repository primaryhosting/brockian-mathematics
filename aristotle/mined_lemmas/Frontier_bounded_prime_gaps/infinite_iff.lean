/-
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring; the header above is repeated
-- verbatim as the module docstring below.)

import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open Filter Set

/-- The `n`-th prime, `p n` (so `p 0 = 2`, `p 1 = 3`, ...). -/

theorem infinite_iff : BoundedPrimeGaps ↔ ∃ B : ℕ, {n | primeGap n ≤ B}.Infinite := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, Set.infinite_of_not_bddAbove ?_⟩
    rintro ⟨M, hM⟩
    obtain ⟨n, hn, hgap⟩ := hB (M + 1)
    have := hM (show n ∈ {n | primeGap n ≤ B} from hgap)
    omega
  · rintro ⟨B, hB⟩
    refine ⟨B, fun N => ?_⟩
    obtain ⟨n, hn, hlt⟩ := hB.exists_gt N
    exact ⟨n, hlt.le, hn⟩

