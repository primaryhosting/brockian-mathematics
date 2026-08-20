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

theorem legendreStatement_iff :
    LegendreStatement ↔
      ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  constructor <;> intro h n hn <;> obtain ⟨p, hp, h1, h2⟩ := h n hn <;>
    exact ⟨p, by simpa [isPrime_iff_natPrime] using hp, h1, h2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Legendre's conjecture holds unconditionally for all `1 ≤ n ≤ 40`, verified by
kernel computation. -/
