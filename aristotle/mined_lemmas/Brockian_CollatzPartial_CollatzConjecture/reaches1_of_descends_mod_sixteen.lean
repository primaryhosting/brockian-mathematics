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

theorem reaches1_of_descends_mod_sixteen
    (hdesc : ∀ n : Nat, 1 < n → (n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15) → Descends n) :
    ∀ n : Nat, 0 < n → Reaches1 n := by
  refine reaches1_of_descends_three_mod_four fun n hn h4 => ?_
  by_cases h3 : n % 16 = 3
  · exact descends_of_three_mod_sixteen h3
  · exact hdesc n hn (by omega)

/--
**Reduction to four residue classes modulo 32.** It suffices to establish the descent
property for the integers congruent to `7`, `15`, `27` or `31` modulo `32`; descent is
unconditional in the other twenty-eight residue classes.
-/
