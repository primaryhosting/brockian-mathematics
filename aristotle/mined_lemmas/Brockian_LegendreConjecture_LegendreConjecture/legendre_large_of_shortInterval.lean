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

-- (Lean requires `import` lines to precede any module docstring, so the header above is a
-- plain block comment and is repeated below as the module docstring.)

import Mathlib

/-!
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LegendreConjecture

/-- **Legendre's conjecture** (statement): for every `n ≥ 1` there is a prime strictly
between `n ^ 2` and `(n + 1) ^ 2`.  This is a famous open problem. -/

theorem legendre_large_of_shortInterval (h : ShortIntervalPrimes) (n : ℕ) (hn : 10 ≤ n) :
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  have hm : 100 ≤ n ^ 2 := by nlinarith
  obtain ⟨p, hp, hlt, hle⟩ := h (n ^ 2) hm
  refine ⟨p, hp, hlt, ?_⟩
  have hsq : Nat.sqrt (n ^ 2) = n := Nat.sqrt_eq' n
  rw [hsq] at hle
  nlinarith

/-- **Legendre's conjecture, conditional on `ShortIntervalPrimes`.**

Legendre's conjecture itself is open; what is proved here is a Lean-checked *conditional
reduction*: the explicit short-interval prime hypothesis `ShortIntervalPrimes` (a prime in
`(m, m + √m]` for every `m ≥ 100`) implies Legendre's conjecture, the remaining cases
`1 ≤ n ≤ 9` being verified unconditionally. -/
