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

namespace CS

/-- A comparison-based sorting algorithm on `n` elements, modelled as a binary decision
tree: an internal node compares two positions `i` and `j` of the input and branches on
the outcome of the test `f i ≤ f j`; a leaf outputs a permutation of the positions,
intended to be the permutation that sorts the input. -/
inductive DTree (n : ℕ) where
  | leaf : Equiv.Perm (Fin n) → DTree n
  | node : Fin n → Fin n → DTree n → DTree n → DTree n
  deriving Inhabited

namespace DTree

variable {n : ℕ}

/-- The worst-case number of comparisons performed by the algorithm, i.e. the height of
the decision tree. -/

lemma perm_eq_one_of_strictMono {n : ℕ} (g : Equiv.Perm (Fin n))
    (h : StrictMono (fun i => ((g i : Fin n) : ℕ))) : g = 1 := by
  refine (Equiv.Perm.monotone_iff g).mp ?_
  intro a b hab
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (Fin.lt_def.mpr (h hlt))

/-- On the input `fun i => (τ i : ℕ)`, a correct comparison sort must output `τ⁻¹`. -/
