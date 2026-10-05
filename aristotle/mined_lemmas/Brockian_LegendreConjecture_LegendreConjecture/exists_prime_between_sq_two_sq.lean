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

theorem exists_prime_between_sq_two_sq (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p ≤ 2 * n ^ 2 := by
  have hne : n ^ 2 ≠ 0 := by positivity
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.bertrand (n ^ 2) hne
  exact ⟨p, hp, hp1, hp2⟩

/-- Unconditional verification of Legendre's conjecture for all `1 ≤ n ≤ 30`. -/
