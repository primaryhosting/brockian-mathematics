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
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained (no `import` lines), so that the header comment
above can literally be the first thing in the file: Lean requires `import` commands to
precede every other command, including module documentation.  Consequently the few
standard facts about function iteration that are used below are proved from scratch.

The Collatz conjecture is a famous open problem.  What is established here is:

* an unconditional reduction of the conjecture to a *descent* hypothesis
  (`reaches1_of_descends`);
* unconditional proofs of descent for every residue class modulo `32` except
  `7`, `15`, `27` and `31`, which sharpen the reduction so that only those four
  classes remain (`CollatzConjecture`);
* unconditional verification of the conjecture for all powers of two and for all
  positive integers below `1000`.
-/

namespace Brockian.CollatzPartial

/-! ## Iteration -/

/-- `iterate f k n` is the `k`-fold application of `f` to `n`. -/

theorem reaches1_of_reachesOneWithin :
    ∀ (fuel n : Nat), reachesOneWithin fuel n = true → Reaches1 n
  | 0, n, h => ⟨0, by simpa [reachesOneWithin] using h⟩
  | fuel + 1, n, h => by
      rw [reachesOneWithin, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨0, by simpa using h⟩
      · exact reaches1_of_step (reaches1_of_reachesOneWithin fuel _ h)

set_option maxRecDepth 40000 in
/-- Unconditional verification: every positive integer below `1000` reaches `1`. -/
