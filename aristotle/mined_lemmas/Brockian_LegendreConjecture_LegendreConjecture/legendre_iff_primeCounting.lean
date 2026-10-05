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
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 forbids a module
-- docstring before `import`; the same header is repeated as a module docstring below.)

import Mathlib

/-!
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Legendre's conjecture — "there is always a prime between two consecutive squares" — is a
well-known open problem.  This file therefore does what can be done rigorously:

* it states the conjecture (`LegendreStatement`);
* it gives several **equivalent reformulations**, including the contrapositive
  ("no prime-free interval between consecutive squares"), a formulation via the
  next-prime function, and a formulation via the prime counting function;
* it gives **conditional reductions**: Legendre's conjecture follows from Andrica's
  conjecture (`LegendreConjecture`, the target theorem) and from a `√m`-size prime gap
  hypothesis;
* it proves **unconditional partial results**: a weakened Bertrand-type version, and a
  verification of the conjecture for all `n ≤ 30`.
-/

namespace Brockian.LegendreConjecture

/-! ## The statement -/

/-- **Legendre's conjecture**: for every `n ≥ 1` there is a prime strictly between
`n ^ 2` and `(n + 1) ^ 2`. -/

theorem legendre_iff_primeCounting :
    LegendreStatement ↔
      ∀ n : ℕ, 1 ≤ n → Nat.primeCounting (n ^ 2) < Nat.primeCounting' ((n + 1) ^ 2) := by
  have key : ∀ n : ℕ, 1 ≤ n →
      ((Nat.primeCounting (n ^ 2) < Nat.primeCounting' ((n + 1) ^ 2)) ↔
        ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2) := by
    intro n hn
    have hab : n ^ 2 + 1 ≤ (n + 1) ^ 2 := by nlinarith
    show Nat.count Nat.Prime (n ^ 2 + 1) < Nat.count Nat.Prime ((n + 1) ^ 2) ↔ _
    rw [count_lt_count_iff Nat.Prime hab]
    constructor
    · rintro ⟨k, hk1, hk2, hk3⟩
      exact ⟨k, hk3, by omega, hk2⟩
    · rintro ⟨p, hp, hp1, hp2⟩
      exact ⟨p, by omega, hp2, hp⟩
  constructor
  · intro h n hn
    exact (key n hn).2 (h n hn)
  · intro h n hn
    exact (key n hn).1 (h n hn)

/-! ## Conditional reductions -/

/-- **Andrica's conjecture** (also open): `√(nextPrime p) - √p < 1` for every prime `p`. -/
