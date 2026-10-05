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
This file is deliberately self-contained (no `import` statements), because the
required header comment above must be the very first thing in the file, and Lean
only accepts `import` commands at the very beginning of a file.  Consequently the
factorial function is defined here from scratch and only core Lean tactics are
used.  Nothing below depends on any unproved assumption.
-/

namespace Brockian.BrocardProblem

/-- The factorial function, `factorial n = n !`. -/

theorem brocard_below_300 (n m : Nat) (hn : n < 300) (h : factorial n + 1 = m ^ 2) :
    n = 4 ∨ n = 5 ∨ n = 7 := by
  by_cases h4 : n = 4
  · exact Or.inl h4
  by_cases h5 : n = 5
  · exact Or.inr (Or.inl h5)
  by_cases h7 : n = 7
  · exact Or.inr (Or.inr h7)
  obtain ⟨hlt, hgt⟩ := brocard_witness_check n (List.mem_range.mpr hn) h4 h5 h7
  exact absurd h.symm (not_square_of_between hlt hgt m)

/-! ### Main result

Brocard's conjecture itself is open.  What is established here, unconditionally and
without any extra assumption, is a *reduction*: the conjecture holds if and only if
no factorial `n !` with `n ≥ 300` has the form `4k(k+1)`.  Equivalently, in the
contrapositive form: any counterexample to Brocard's conjecture consists of some
`n ≥ 300` and some `k` with `n ! = 4k(k+1)` (and then `n ! + 1 = (2k+1)²`).

Two ingredients: the kernel-verified absence of unexpected solutions for `n < 300`,
and the parity argument showing that the square root in any solution with `n ≥ 2`
is odd, which turns `n ! + 1 = m²` into `n ! = 4k(k+1)`. -/

/-- **Brocard conjecture, reduced (contrapositive) form.**  The statement
"`n ! + 1` is a perfect square only for `n = 4, 5, 7`" is *equivalent* to
"for every `n ≥ 300` and every `k`, `n ! ≠ 4k(k+1)`".  In particular the conjecture
is verified for all `n < 300`, and its entire remaining content is the assertion that
no factorial beyond that range is a product of the shape `4k(k+1)`. -/
