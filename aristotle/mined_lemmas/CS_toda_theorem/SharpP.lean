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

def SharpP (f : (n : ℕ) → (Fin n → Bool) → ℕ) : Prop :=
  ∃ (M : ℕ → ℕ) (V : ℕ → Circ), PolyBd M ∧ PolySize V ∧
    ∀ (n : ℕ) (x : Fin n → Bool), f n x = cnt (V n) (inp x) n (M n)

/-! ### Oracle machines and `P^{#P}` -/

/-- A (nonuniform) polynomial-time oracle machine: it makes `t` adaptive queries of length
`qlen` to the oracle, keeping `abits` bits of each answer.  Bit `c` of query `i` is computed
by the formula `Q i c` from the input together with the answer bits of the earlier queries,
which are stored in consecutive blocks starting at offset `base`.  The formula `out`
computes the final answer. -/
structure OMach where
  /-- number of oracle queries -/
  t : ℕ
  /-- length of each query string -/
  qlen : ℕ
  /-- number of bits kept from each answer -/
  abits : ℕ
  /-- offset at which the answer blocks are stored -/
  base : ℕ
  /-- `Q i c` computes bit `c` of the `i`-th query -/
  Q : ℕ → ℕ → Circ
  /-- output formula -/
  out : Circ

namespace OMach

/-- The assignment after `i` oracle queries have been answered. -/
