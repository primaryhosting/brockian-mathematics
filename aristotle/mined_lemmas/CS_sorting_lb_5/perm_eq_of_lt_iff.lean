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

/-- A comparison-sorting algorithm on `n` elements, modelled as a binary decision tree.

The hidden input is a permutation `σ : Equiv.Perm (Fin n)`, thought of as the ranking of the
`n` input elements: element `i` has rank `σ i`.  An internal node `node i j l r` compares
elements `i` and `j`; the algorithm continues in `l` if `σ i < σ j` and in `r` otherwise.
A leaf reports the permutation the algorithm has decided the input is. -/
inductive CTree (n : ℕ) : Type
  | leaf (p : Equiv.Perm (Fin n)) : CTree n
  | node (i j : Fin n) (l r : CTree n) : CTree n
  deriving Inhabited

namespace CTree

variable {n : ℕ}

/-- The output of the algorithm `t` on the input ranking `σ`. -/

theorem perm_eq_of_lt_iff {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
    (h : ∀ i j : Fin n, τ i < τ j ↔ σ i < σ j) : τ = σ := by
  have hmono : StrictMono (fun x : Fin n => τ (σ.symm x)) := by
    intro a b hab
    have : σ (σ.symm a) < σ (σ.symm b) := by simpa using hab
    exact (h _ _).2 this
  have hid : ∀ x : Fin n, τ (σ.symm x) = x := by
    intro x
    have h1 : x ≤ τ (σ.symm x) := hmono.le_apply
    have h2 : τ (σ.symm x) ≤ x := hmono.dual.le_apply (β := (Fin n)ᵒᵈ)
    exact le_antisymm h2 h1
  refine Equiv.ext fun x => ?_
  simpa using hid (σ x)

/-- The model is not vacuous: for every `n` there is a correct comparison-sorting decision
tree on `n` elements. -/
