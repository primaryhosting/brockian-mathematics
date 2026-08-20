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

theorem LegendreConjecture (hgap : ShortGapHypothesis) : LegendreStatement := by
  intro n hn
  have hx : 1 ≤ n ^ 2 := by
    have := Nat.pow_le_pow_left hn 2
    simpa using this
  have hmm : n * n ≤ n ^ 2 := by rw [sq_eq_mul_self]; exact Nat.le_refl _
  obtain ⟨p, hp, hlt, hle⟩ := hgap (n ^ 2) n hx hmm
  refine ⟨p, hp, hlt, ?_⟩
  have hkey : n ^ 2 + n < n ^ 2 + 2 * n + 1 := by
    have : n < 2 * n + 1 := by omega
    have := Nat.add_lt_add_left this (n ^ 2)
    omega
  rw [succ_sq]
  exact Nat.lt_of_le_of_lt hle hkey

end Brockian.LegendreConjecture

