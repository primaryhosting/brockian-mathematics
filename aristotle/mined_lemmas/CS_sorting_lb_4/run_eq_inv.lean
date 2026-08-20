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

lemma run_eq_inv {n : ℕ} (t : DTree n) (ht : Sorts t) (τ : Equiv.Perm (Fin n)) :
    t.run (fun i => ((τ i : Fin n) : ℕ)) = τ⁻¹ := by
  set f : Fin n → ℕ := fun i => ((τ i : Fin n) : ℕ) with hf
  have hinj : Function.Injective f := by
    intro a b hab
    have : τ a = τ b := Fin.val_injective hab
    exact τ.injective this
  have hsm := ht f hinj
  set σ := t.run f with hσ
  have : StrictMono (fun i => (((τ * σ) i : Fin n) : ℕ)) := by
    simpa [Function.comp, hf, Equiv.Perm.mul_apply] using hsm
  have h1 : τ * σ = 1 := perm_eq_one_of_strictMono _ this
  have := congrArg (fun p => τ⁻¹ * p) h1
  simpa [← mul_assoc] using this

/-- **Comparison-sort lower bound for 4 elements.**
Any correct comparison sort of `4` elements uses at least `⌈log₂ (4!)⌉ = 5` comparisons
in the worst case. -/
