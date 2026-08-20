import RequestProject.Degree

open Finset

namespace Frontier

/-! # Huang's sensitivity theorem: `s(f) ≥ √(deg f)`

Using the full-degree case `Frontier.huang_sensitivity` together with a restriction argument
to a subcube, we obtain the general statement: the sensitivity of a Boolean function is at
least the square root of its degree.
-/

section Coeff

variable {n : ℕ}

/-- Uniqueness of the multilinear representation. -/

theorem sensitivity_and_two : Real.sqrt 2 ≤ sensitivity (fun x : Q 2 => x 0 && x 1) := by
  have h2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [← h2]
  refine huang_sensitivity (by norm_num) _ ?_
  intro hdeg
  have h := topSum_eq_zero_of_hasDegLE (n := 2) (by norm_num) hdeg
  rw [topSum_eq (by norm_num)] at h
  have hcard : (univ.filter (fun x : Q 2 => (x 0 && x 1) ≠ par x)).card = 3 := by decide
  rw [hcard] at h
  norm_num at h

end Degree

end Frontier

import Mathlib
import RequestProject.Huang
import RequestProject.Degree
import RequestProject.Full

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

open Finset

namespace Frontier

/-! # Huang's sensitivity theorem (the `deg = n` case)

We formalise Huang's 2019 theorem.  The combinatorial core is:

* `Frontier.huang_cube` : every set `S` of more than `2^(n-1)` vertices of the Boolean
  hypercube `{0,1}^n` contains a vertex with at least `√n` neighbours inside `S`.

From it we deduce the sensitivity statement `Frontier.huang_sensitivity`.
-/

/-- Vertices of the `n`-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Flip the `i`-th coordinate of a hypercube vertex. -/
