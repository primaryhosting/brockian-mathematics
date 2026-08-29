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
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.GilbreathConjecture

/-- Absolute difference of two natural numbers, written without `Int`. -/

theorem stable_of_le {N n : ℕ} (hN : Stable N) (h : N ≤ n) : Stable n := by
  induction n with
  | zero => simpa [Nat.le_zero.mp h] using hN
  | succ m ih =>
    rcases Nat.lt_or_ge N (m + 1) with hlt | hge
    · exact stable_succ (ih (by omega))
    · have : N = m + 1 := le_antisymm h hge
      exact this ▸ hN

set_option linter.dupNamespace false in
/-- **Conditional reduction of Gilbreath's conjecture.**
If some row `N ≥ 1` of the Gilbreath triangle has the form `1, x₁, x₂, …` with every
`xᵢ ∈ {0, 2}`, and every row from the first up to row `N` starts with `1`, then
Gilbreath's conjecture holds: every row after the zeroth starts with `1`.

(The hypotheses are exactly the "stabilization" property that all numerical evidence for
the conjecture is based on; the unconditional statement remains open.) -/
