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

theorem boundedPrimePairs_iff : BoundedPrimeGaps ↔ BoundedPrimePairs := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, fun N => ?_⟩
    obtain ⟨n, hn, hgap⟩ := hB N
    refine ⟨nthPrime n, nthPrime (n + 1), nthPrime_prime n, nthPrime_prime (n + 1), ?_,
      nthPrime_strictMono (Nat.lt_succ_self n), hgap⟩
    exact hn.trans (le_nthPrime n)
  · rintro ⟨B, hB⟩
    refine ⟨B, fun N => ?_⟩
    obtain ⟨p, q, hp, hq, hNp, hpq, hqp⟩ := hB (nthPrime N)
    set k := Nat.count Nat.Prime p with hk
    have hnk : nthPrime k = p := nthPrime_count hp
    have hkN : N ≤ k := by
      by_contra hlt
      push_neg at hlt
      have : nthPrime k < nthPrime N := nthPrime_strictMono hlt
      omega
    refine ⟨k, hkN, ?_⟩
    have h1 : nthPrime (k + 1) ≤ q := nthPrime_succ_count_le hp hq hpq
    simp only [primeGap, hnk]
    omega

/-! ### Equivalent analytic formulations -/

