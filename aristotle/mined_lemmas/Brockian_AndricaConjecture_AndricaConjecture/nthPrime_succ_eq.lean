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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not allow a
-- module docstring to precede the `import` line.)

import Mathlib

namespace Brockian.AndricaConjecture

open scoped Nat

/-! ## The sequence of primes -/

/-- The set of primes is infinite. -/

theorem nthPrime_succ_eq {n q : ℕ} (hq : Nat.Prime q) (hlt : nthPrime n < q)
    (hgap : ∀ m, nthPrime n < m → m < q → ¬ Nat.Prime m) : nthPrime (n + 1) = q := by
  have hle : nthPrime (n + 1) ≤ q := nthPrime_succ_le hq hlt
  rcases lt_or_eq_of_le hle with h | h
  · exact absurd (nthPrime_prime (n + 1)) (hgap _ (nthPrime_lt_nthPrime_succ n) h)
  · exact h

