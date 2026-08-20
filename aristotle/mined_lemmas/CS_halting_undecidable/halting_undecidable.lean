/-
# Halting Undecidable
Category: Computer Science
Target: CS.halting_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is a plain block comment because Lean requires `import` to come first;
-- the same text is repeated below as a module docstring.)

import Mathlib

/-!
# Halting Undecidable
Category: Computer Science
Target: CS.halting_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace CS

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- **The halting problem is undecidable.**

There is no total computable function `H : Code → ℕ → Bool` which, given (a code for)
a program `p` and an input `x`, decides whether `p` halts on `x`
(i.e. whether the partial function `eval p` is defined at `x`).

The proof reduces to Mathlib's `ComputablePred.halting_problem`, which states that for each
fixed input `n` the predicate `fun c => (eval c n).Dom` is not computable; that result in turn
is obtained from Rice's theorem, whose proof is the usual diagonalization / fixed-point
(Kleene recursion theorem) argument. -/

theorem halting_undecidable :
    ¬ ∃ H : Code → ℕ → Bool,
        Computable₂ H ∧ ∀ (p : Code) (x : ℕ), H p x = true ↔ (eval p x).Dom := by
  rintro ⟨H, hH, hspec⟩
  refine ComputablePred.halting_problem 0 ?_
  refine ComputablePred.computable_iff.2 ⟨fun c => H c 0, ?_, ?_⟩
  · exact hH.comp Computable.id (Computable.const 0)
  · funext c
    simpa using (hspec c 0).symm

/-- A variant phrased with a `ℕ`-valued decider, using the standard numbering of partial
recursive functions: there is no total computable `H : ℕ → ℕ → ℕ` with
`H p x = 1` exactly when the program with code number `p` halts on input `x`. -/
