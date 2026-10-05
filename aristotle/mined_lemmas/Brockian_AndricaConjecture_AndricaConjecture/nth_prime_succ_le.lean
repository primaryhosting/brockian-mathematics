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

import Mathlib

/-!
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AndricaConjecture

/-- **Oppermann's conjecture** (open): for every `n ≥ 2` there is a prime strictly between
`n²` and `n² + n`, and a prime strictly between `n² + n` and `(n+1)²`. -/

lemma nth_prime_succ_le {n q : ℕ} (hq : q.Prime) (h : Nat.nth Nat.Prime n < q) :
    Nat.nth Nat.Prime (n + 1) ≤ q := by
  have hcount : Nat.nth Nat.Prime (Nat.count Nat.Prime q) = q := Nat.nth_count hq
  have hlt : n < Nat.count Nat.Prime q := by
    rw [← Nat.nth_lt_nth Nat.infinite_setOf_prime (k := n) (n := Nat.count Nat.Prime q), hcount]
    exact h
  calc Nat.nth Nat.Prime (n + 1) ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime q) :=
        (Nat.nth_le_nth Nat.infinite_setOf_prime).2 (by omega)
    _ = q := hcount

/-- Unconditional criterion: Andrica's inequality holds at `n` as soon as the prime gap
satisfies `pₙ₊₁ < pₙ + 2⌊√pₙ⌋ + 1`. -/
