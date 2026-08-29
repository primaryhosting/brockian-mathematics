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

def eval (v : ℕ → Bool) : Circ → Bool
  | .var i => v i
  | .cst b => b
  | .neg a => !(a.eval v)
  | .conj a b => (a.eval v) && (b.eval v)
  | .disj a b => (a.eval v) || (b.eval v)
  | .xorC a b => xor (a.eval v) (b.eval v)

def asg (x : List Bool) {m : ℕ} (y : Fin m → Bool) (i : ℕ) : Bool :=
  if i < x.length then x.getD i false
  else if h : i - x.length < m then y ⟨i - x.length, h⟩ else false

/-- Number of witnesses `y ∈ {0,1}^m` accepted by `C` on input `x`. -/

def cnt (C : Circ) (m : ℕ) (x : List Bool) : ℕ :=
  ∑ y : Fin m → Bool, (if C.eval (asg x y) then 1 else 0)

theorem cnt_le (C : Circ) (m : ℕ) (x : List Bool) : cnt C m x ≤ 2 ^ m := by
  classical
  have h : cnt C m x ≤ ∑ _y : Fin m → Bool, 1 := by
    apply Finset.sum_le_sum
    intro y _
    split <;> simp
  simpa [Fintype.card_fun] using h

end CS
