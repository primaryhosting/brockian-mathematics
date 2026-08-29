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

lemma bitMach_accepts (f : (n : ℕ) → (Fin n → Bool) → ℕ) (n j : ℕ) (x : Fin n → Bool) :
    (bitMach n j).accepts f (inp x) = Nat.testBit (f n x) j := by
  show Circ.eval (Circ.var (n + j)) _ = _
  simp only [OMach.state, Circ.eval_var, bitMach]
  have hx : (fun c : Fin n => (Circ.var (c : ℕ)).eval (inp x)) = x := by
    funext c
    simp
  rw [hx]
  have := ext_mem (inp x) (n + 0 * (j + 1))
    (fun k : Fin (j + 1) => Nat.testBit (f n x) k) ⟨j, by omega⟩
  simpa using this

/-- If a language is decided by taking one prescribed bit of the value of a `#P` function
on the input itself, then it lies in `P^{#P}`. -/
