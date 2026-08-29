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

import Mathlib

/-!
# Boolean circuits (formulas) and block-structured witness counting

This file sets up the elementary infrastructure used in the formalization of Toda's
theorem: a datatype of boolean formulas over variables indexed by `ℕ`, variable
substitution, big conjunctions/disjunctions, assignments extended by "blocks" of
witness bits, and counting of satisfying blocks.
-/

open scoped BigOperators

namespace CS

/-- Boolean formulas over variables indexed by `ℕ`. -/
inductive Circ where
  | fls : Circ
  | tru : Circ
  | var : ℕ → Circ
  | neg : Circ → Circ
  | conj : Circ → Circ → Circ
  | disj : Circ → Circ → Circ
  | xorC : Circ → Circ → Circ
  deriving Inhabited

namespace Circ

/-- Value of a formula under an assignment. -/

@[simp] lemma altSat_cons_false (qs : List Bool) (off m : ℕ) (α : ℕ → Bool) (C : Circ) :
    altSat (false :: qs) off m α C ↔
      ∀ y : Fin m → Bool, altSat qs (off + m) m (ext α off y) C := by
  simp [altSat]

/-- The polynomial hierarchy (in the circuit model): languages defined by a constant
number of alternating quantifiers over polynomially long witnesses, with a
polynomial-size matrix. -/
