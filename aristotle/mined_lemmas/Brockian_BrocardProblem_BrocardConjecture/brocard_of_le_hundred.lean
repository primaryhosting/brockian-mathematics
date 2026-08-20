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
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.BrocardProblem

open Nat

set_option maxRecDepth 100000

/-- The statement of Brocard's conjecture: the only natural numbers `n` for which
`n! + 1` is a perfect square are `n = 4`, `n = 5` and `n = 7`
(with `4! + 1 = 5²`, `5! + 1 = 11²`, `7! + 1 = 71²`). -/

theorem brocard_of_le_hundred (n m : ℕ) (hn : n ≤ 100) (h : n ! + 1 = m ^ 2) :
    n = 4 ∨ n = 5 ∨ n = 7 := by
  by_cases h8 : 8 ≤ n
  · exact absurd h (factorial_succ_not_sq_of_le_hundred n h8 hn m)
  · push_neg at h8
    interval_cases n
    · exact absurd h (not_sq_of_between (k := 1) (by decide) (by decide) m)
    · exact absurd h (not_sq_of_between (k := 1) (by decide) (by decide) m)
    · exact absurd h (not_sq_of_between (k := 1) (by decide) (by decide) m)
    · exact absurd h (not_sq_of_between (k := 2) (by decide) (by decide) m)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd h (not_sq_of_between (k := 26) (by decide) (by decide) m)
    · exact Or.inr (Or.inr rfl)

/-- **Brocard's conjecture, conditional on the pronic reduction.**

Brocard's problem asks for all `n` such that `n! + 1` is a perfect square; the conjecture is
that `n = 4, 5, 7` are the only ones.  This is a long-standing open problem, so what is proved
here is a Lean-checked *conditional reduction*: assuming that for `n ≥ 101` the factorial `n!`
is never four times a pronic number, i.e. never of the form `4a(a+1)`, Brocard's conjecture
holds.  All cases `n ≤ 100` are verified unconditionally inside the proof, and by
`factorial_succ_isSquare_iff_pronic` the hypothesis is exactly the content of the
remaining cases. -/
