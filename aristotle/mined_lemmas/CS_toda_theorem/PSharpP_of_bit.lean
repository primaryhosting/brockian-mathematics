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

lemma PSharpP_of_bit {L : Lang} {f : (n : ℕ) → (Fin n → Bool) → ℕ} (hf : SharpP f)
    {j : ℕ → ℕ} (hj : PolyBd j)
    (h : ∀ (n : ℕ) (x : Fin n → Bool), L n x ↔ Nat.testBit (f n x) (j n) = true) :
    PSharpP L := by
  classical
  refine ⟨f, hf, fun n => bitMach n (j n), ?_, ?_⟩
  · refine PolyBd.mono (g := fun n => 1 + n + (j n + 1) + 1 + n + n)
      (PolyBd.add (PolyBd.add (PolyBd.add (PolyBd.add (PolyBd.add
        (PolyBd.const 1) PolyBd.id') (PolyBd.add hj (PolyBd.const 1)))
        (PolyBd.const 1)) PolyBd.id') PolyBd.id') ?_
    intro n
    exact le_of_eq (bitMach_size n (j n))
  · intro n x
    rw [h n x, bitMach_accepts]

end CS

