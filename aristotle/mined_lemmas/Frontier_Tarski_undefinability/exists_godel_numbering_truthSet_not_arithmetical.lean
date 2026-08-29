/-
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open FirstOrder Language

namespace Frontier

/-! ## The language of arithmetic and its standard model -/

/-- The function symbols of the language of arithmetic: `0`, `1`, `+`, `*`. -/
inductive arithFunc : ℕ → Type
  | zero : arithFunc 0
  | one : arithFunc 0
  | add : arithFunc 2
  | mul : arithFunc 2
  deriving DecidableEq

/-- The (purely functional) first-order language of arithmetic, with symbols `0`, `1`, `+`, `*`. -/

theorem exists_godel_numbering_truthSet_not_arithmetical :
    ∃ enc : arith.Formula (Fin 1) → ℕ,
      Function.Injective enc ∧ ¬ Arithmetical (truthSet enc) := by
  obtain ⟨enc, henc⟩ := exists_injective_nat (arith.Formula (Fin 1))
  exact ⟨enc, henc, Tarski_undefinability enc henc⟩

end Frontier

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

