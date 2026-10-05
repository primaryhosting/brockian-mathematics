/-
# Halting Undecidable
Category: Computer Science
Target: CS.halting_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- **The halting problem is undecidable.**

There is no total computable function `H` of two arguments (a program `p`, given as a
partial-recursive code, and an input `x`) that decides whether `p` halts on `x`.

The proof reduces to `ComputablePred.halting_problem`, whose Mathlib proof is the usual
diagonalization via Kleene's recursion theorem (`Nat.Partrec.Code.fixed_point`):
if such an `H` existed, then fixing the input `0` would make the predicate
`fun p => (p.eval 0).Dom` computable, which is impossible. -/
theorem halting_undecidable :
    ¬ ∃ H : Code → ℕ → Bool, Computable₂ H ∧
        ∀ (p : Code) (x : ℕ), H p x = true ↔ (p.eval x).Dom := by
  rintro ⟨H, hH, hspec⟩
  -- Specialize the decider to the fixed input `0`.
  refine ComputablePred.halting_problem 0 ?_
  rw [ComputablePred.computable_iff]
  exact ⟨fun p => H p 0, hH.comp Computable.id (Computable.const 0),
    funext fun p => propext (hspec p 0).symm⟩

/-- The same statement with programs presented as natural-number indices (Gödel numbers),
decoded through the standard numbering of partial recursive codes. -/
theorem halting_undecidable_nat :
    ¬ ∃ H : ℕ → ℕ → Bool, Computable₂ H ∧
        ∀ (e x : ℕ), H e x = true ↔ ((Denumerable.ofNat Code e).eval x).Dom := by
  rintro ⟨H, hH, hspec⟩
  refine halting_undecidable ⟨fun p x => H (Encodable.encode p) x, ?_, ?_⟩
  · exact hH.comp (Computable.encode.comp (Computable.fst)) Computable.snd
  · intro p x
    simpa using hspec (Encodable.encode p) x

end CS

