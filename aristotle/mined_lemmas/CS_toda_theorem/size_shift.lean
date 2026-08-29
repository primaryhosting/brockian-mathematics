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
# Boolean circuits (formulas) over natural-number-indexed variables

This file sets up the basic combinatorial machinery used in the formalisation of
Toda's theorem: Boolean formulas over variables indexed by `ℕ`, their size,
their variable bound, evaluation, and the *counting* operation
`cnt C m x` = number of witnesses `y ∈ {0,1}^m` making `C` true on input `x`.
-/

namespace CS

open Finset

/-- Boolean formulas over variables indexed by `ℕ`. -/
inductive Circ where
  | var (i : ℕ) : Circ
  | cst (b : Bool) : Circ
  | neg (a : Circ) : Circ
  | conj (a b : Circ) : Circ
  | disj (a b : Circ) : Circ
  | xorC (a b : Circ) : Circ
  deriving Inhabited

namespace Circ

/-- Evaluation of a formula under an assignment. -/

@[simp] theorem size_shift (n d : ℕ) (C : Circ) : (shift n d C).size = C.size := by
  induction C with
  | var i => rfl
  | cst b => rfl
  | neg a ih => simp [shift, size, ih]
  | conj a b iha ihb => simp [shift, size, iha, ihb]
  | disj a b iha ihb => simp [shift, size, iha, ihb]
  | xorC a b iha ihb => simp [shift, size, iha, ihb]

