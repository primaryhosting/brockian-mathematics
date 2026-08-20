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

def LegendreStatement : Prop :=
  ∀ n : Nat, 1 ≤ n → ∃ p : Nat, IsPrime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2

/-- A short prime gap hypothesis: for every `x ≥ 1` there is a prime in the interval
`(x, x + √x]`, where `√x` is expressed by an auxiliary `m` with `m * m ≤ x`.
This is itself an open problem — it is far beyond what is currently known
unconditionally, and it is slightly stronger than Legendre's conjecture. -/
