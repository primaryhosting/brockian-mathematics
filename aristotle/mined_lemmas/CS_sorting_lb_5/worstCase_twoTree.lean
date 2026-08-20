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

/-! ## Comparison sorts as decision trees

An input to a comparison sort on `n` elements is modelled by a permutation
`σ : Equiv.Perm (Fin n)`, where `σ i` is the rank of the `i`-th input element (so the
input is in "general position": all elements are distinct).  A deterministic
comparison-based sorting algorithm is a binary decision tree: each internal node asks a
comparison "is the `i`-th element ≤ the `j`-th element?" and branches accordingly, and each
leaf outputs a permutation (the algorithm's verdict about the ranking of the input).
-/

/-- A comparison-based decision tree on `n` elements.  Internal nodes compare two positions,
leaves output a permutation. -/
inductive DTree (n : ℕ) where
  | leaf : Equiv.Perm (Fin n) → DTree n
  | node : Fin n → Fin n → DTree n → DTree n → DTree n

/-- The output of the algorithm `t` on the input whose ranking is `σ`. -/

theorem worstCase_twoTree : worstCase twoTree = 1 := by
  have h : ∀ σ : Equiv.Perm (Fin 2), comps twoTree σ = 1 := by
    intro σ; fin_cases σ <;> decide
  have hf : comps twoTree = fun _ => 1 := funext h
  rw [worstCase, hf, Finset.sup_const Finset.univ_nonempty]

end CS

