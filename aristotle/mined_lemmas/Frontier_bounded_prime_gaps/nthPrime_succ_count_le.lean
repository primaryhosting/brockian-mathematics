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

theorem nthPrime_succ_count_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    nthPrime (Nat.count Nat.Prime p + 1) ≤ q := by
  have hstep : Nat.count Nat.Prime (p + 1) = Nat.count Nat.Prime p + 1 := by
    simp [Nat.count_succ, hp]
  have hmono : Nat.count Nat.Prime (p + 1) ≤ Nat.count Nat.Prime q :=
    Nat.count_monotone _ hpq
  calc nthPrime (Nat.count Nat.Prime p + 1)
      ≤ nthPrime (Nat.count Nat.Prime q) := nthPrime_le_nthPrime.2 (by omega)
    _ = q := nthPrime_count hq

