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

theorem bnd_shift {n d m : ℕ} {C : Circ} (h : C.bnd ≤ n + m) :
    (shift n d C).bnd ≤ n + d + m := by
  induction C with
  | var i =>
      simp only [bnd] at h
      by_cases hi : i < n
      · simp only [shift, if_pos hi, bnd]; omega
      · simp only [shift, if_neg hi, bnd]; omega
  | cst b => simp [shift, bnd]
  | neg a ih => exact ih h
  | conj a b iha ihb =>
      simp only [bnd, max_le_iff] at h
      simp only [shift, bnd, max_le_iff]
      exact ⟨iha h.1, ihb h.2⟩
  | disj a b iha ihb =>
      simp only [bnd, max_le_iff] at h
      simp only [shift, bnd, max_le_iff]
      exact ⟨iha h.1, ihb h.2⟩
  | xorC a b iha ihb =>
      simp only [bnd, max_le_iff] at h
      simp only [shift, bnd, max_le_iff]
      exact ⟨iha h.1, ihb h.2⟩

end Circ

/-- The assignment determined by an input string `x` (variables `0, …, |x|-1`)
together with a witness `y ∈ {0,1}^m` (variables `|x|, …, |x|+m-1`).
Out-of-range variables get the value `false`. -/
