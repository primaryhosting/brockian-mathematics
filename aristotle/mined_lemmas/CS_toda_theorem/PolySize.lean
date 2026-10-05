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

def PolySize (C : ℕ → Circ) : Prop := PolyBd (fun n => (C n).size)

end CS

import RequestProject.Toda.Circuit

/-!
# The complexity classes `PH`, `#P` and `P^{#P}`

We work in the (standard) nonuniform circuit model: a *language* assigns to every input
length `n` a predicate on `n`-bit inputs, and "polynomial time" is modelled by families of
boolean formulas of polynomial size (i.e. `P/poly`).  All classes below are the
circuit analogues of the usual uniform ones.
-/

open scoped BigOperators

namespace CS

/-- A language: for every input length, a predicate on inputs of that length. -/
