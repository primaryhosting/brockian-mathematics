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
import Brockian.LegendreConjecture

/-!
# Legendre Conjecture — Mathlib companion

This module connects the self-contained statements of `Brockian.LegendreConjecture`
(which, by design, imports nothing so that the required header comment can sit at the
very top of that file) with Mathlib's `Nat.Prime`, and records some unconditional
partial results towards Legendre's conjecture.
-/

namespace Brockian.LegendreConjecture

/-- The self-contained primality predicate used in `Brockian.LegendreConjecture`
agrees with Mathlib's `Nat.Prime`. -/

theorem succ_sq (n : Nat) : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by
  simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_add, Nat.add_mul]
  omega

/-- **Conditional reduction of Legendre's conjecture.**

Legendre's conjecture — the existence, for every `n ≥ 1`, of a prime strictly between
`n ^ 2` and `(n + 1) ^ 2` — is an open problem, so it is established here
*conditionally*: it follows from the short prime gap hypothesis
`ShortGapHypothesis`, which asserts a prime in `(x, x + √x]` for every `x ≥ 1`.
Applying that hypothesis at `x = n ^ 2` (with `√x = n`) produces a prime `p` with
`n ^ 2 < p ≤ n ^ 2 + n < (n + 1) ^ 2`. -/
