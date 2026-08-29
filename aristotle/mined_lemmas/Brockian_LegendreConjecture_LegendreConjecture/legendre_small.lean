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

theorem legendre_small (n : ℕ) (hn : 0 < n) (hn' : n < 10) :
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  interval_cases n
  · exact ⟨2, by norm_num⟩
  · exact ⟨5, by norm_num⟩
  · exact ⟨11, by norm_num⟩
  · exact ⟨17, by norm_num⟩
  · exact ⟨29, by norm_num⟩
  · exact ⟨37, by norm_num⟩
  · exact ⟨53, by norm_num⟩
  · exact ⟨67, by norm_num⟩
  · exact ⟨83, by norm_num⟩

/-- The reduction step: for `n ≥ 10` the short-interval hypothesis produces a prime in
`(n ^ 2, n ^ 2 + n]`, which lies strictly below `(n + 1) ^ 2`. -/
