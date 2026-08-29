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
# Halting Undecidable
Category: Computer Science
Target: CS.halting_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Halting Undecidable
Category: Computer Science
Target: CS.halting_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Nat.Partrec Code Denumerable Encodable

/-- The diagonal partial function associated to a candidate halting decider `H`:
on input `n` it diverges exactly when `H` claims that the `n`-th program halts on
input `n`, and returns `0` otherwise. -/

theorem diag_dom_iff (H : Code → ℕ → Bool) (n : ℕ) :
    (diag H n).Dom ↔ H (ofNat Code n) n = false := by
  unfold diag
  cases h : H (ofNat Code n) n <;> simp

/-- **The halting problem is undecidable.**
There is no total computable function `H` which, given (a code for) a program `p`
and an input `x`, decides whether `p` halts on `x`.  The proof is by
diagonalization: from such an `H` one builds a program that halts on its own code
exactly when `H` says it does not. -/
