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

/-!
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained: it uses only the Lean 4 core library
(no `import` is possible before the required header comment above), so the factorial
function is defined here from scratch.

Brocard's problem asks for all solutions of `n ! + 1 = m ^ 2`; the conjecture (open) is that
`(n, m) = (4, 5), (5, 11), (7, 71)` are the only ones.  What is proved below is:

* `brocard_iff_pronic` : for `n ≥ 2`, `n ! + 1` is a square iff `n ! = 4 * a * (a + 1)`
  for some `a` (an unconditional reduction of the equation to a pronic form);
* `brocard_le_hundred` : an unconditional verification of the conjecture for all `n ≤ 100`;
* `BrocardConjecture` : the full conjecture, conditional on the reduced (pronic) equation
  having no solutions for `n ≥ 101`.
-/

namespace Brockian.BrocardProblem

/-- The factorial function, `fact n = n !`. -/

theorem fact_even {n : Nat} (hn : 2 ≤ n) : ∃ k, fact n = 2 * k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · have hn1 : n = 1 := by omega
      subst hn1
      exact ⟨1, by decide⟩
    · obtain ⟨k, hk⟩ := ih h
      exact ⟨(n + 1) * k, by rw [fact_succ, hk]; grind⟩

/-- **Reduction to a pronic equation.**  For `n ≥ 2`, `n ! + 1` is a perfect square exactly when
`n !` is four times a product of two consecutive integers. -/
