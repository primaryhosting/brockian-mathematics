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

theorem brocard_iff_pronic {n : Nat} (hn : 2 ≤ n) :
    (∃ m, fact n + 1 = m ^ 2) ↔ ∃ a : Nat, fact n = 4 * a * (a + 1) := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨k, hk⟩ := fact_even hn
    have hmodd : m % 2 = 1 := by
      rcases (by omega : m % 2 = 0 ∨ m % 2 = 1) with h0 | h1
      · exfalso
        obtain ⟨t, ht⟩ : ∃ t, m = 2 * t := ⟨m / 2, by omega⟩
        subst ht
        have hexp : (2 * t) ^ 2 = 4 * (t * t) := by grind
        omega
      · exact h1
    obtain ⟨a, ha⟩ : ∃ a, m = 2 * a + 1 := ⟨m / 2, by omega⟩
    subst ha
    refine ⟨a, ?_⟩
    have hexp : (2 * a + 1) ^ 2 = 4 * a * (a + 1) + 1 := by grind
    omega
  · rintro ⟨a, ha⟩
    refine ⟨2 * a + 1, ?_⟩
    rw [ha]
    grind

/-- The three known solutions of Brocard's equation. -/
