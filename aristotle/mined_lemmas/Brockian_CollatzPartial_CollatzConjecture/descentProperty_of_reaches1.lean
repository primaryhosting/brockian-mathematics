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
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The full Collatz conjecture is open.  What is proved here is:

* `CollatzConjecture` : a Lean-checked *conditional reduction* — if every integer `> 1`
  eventually iterates to a strictly smaller value (the descent property), then every
  positive integer reaches `1`.
* unconditional partial results: the descent property holds for every `n > 1` outside the
  residue class `3 (mod 4)`, and every power of two reaches `1`.
-/

namespace Brockian.CollatzPartial

/-- One step of the Collatz map: `n ↦ n/2` if `n` is even, `n ↦ 3n+1` if `n` is odd. -/

theorem descentProperty_of_reaches1 (h : ∀ n : ℕ, 0 < n → Reaches1 n) : DescentProperty := by
  intro n hn
  obtain ⟨k, hk⟩ := h n (by omega)
  refine ⟨k, ?_, by rw [hk]; omega⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp at hk; omega
  · exact hk0

/-- The Collatz conjecture is equivalent to the descent property. -/
