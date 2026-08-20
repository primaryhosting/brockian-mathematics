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

/-!
# Sperner's lemma

Every Sperner colouring of a triangulated simplex has an odd number of rainbow cells.
-/

namespace Math

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of cells of `T` containing the face `F`. -/

def IsSpernerTriangulation (c : V → ℕ) (car : V → Finset ℕ) : ℕ → Finset (Finset V) → Prop
  | 0, T => ∃ v : V, T = {{v}} ∧ c v = 0
  | (n + 1), T =>
      (∀ σ ∈ T, σ.card = n + 2) ∧
      (∀ σ ∈ T, ∀ v ∈ σ, c v ∈ car v ∧ car v ⊆ Finset.range (n + 2)) ∧
      (∀ F : Finset V, (∃ σ ∈ T, F ⊆ σ) → F.card = n + 1 → Odd (cellMult T F) →
        ∃ i < n + 2, ∀ v ∈ F, i ∉ car v) ∧
      IsSpernerTriangulation c car n (bdry car n T)

/-- The potential "doors": faces of size `n+1` carrying exactly the colours `0, …, n`. -/
