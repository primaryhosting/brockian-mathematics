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

set_option maxRecDepth 10000
set_option synthInstance.maxSize 400
set_option synthInstance.maxHeartbeats 1000000

namespace Math

open Finset SimpleGraph

/-- `HasRamseyProp34 n` holds when every simple graph on `n` vertices contains either a
clique of size `3` or an independent set of size `4`; equivalently, every red/blue colouring
of the edges of `K n` contains a red triangle or a blue `K 4`. -/

def G8 : SimpleGraph (Fin 8) where
  Adj a b := ((a.val + 8 - b.val) % 8) ∈ ({1, 4, 7} : Finset ℕ)
  symm := by
    have h : ∀ x y : Fin 8, ((x.val + 8 - y.val) % 8) ∈ ({1, 4, 7} : Finset ℕ) →
        ((y.val + 8 - x.val) % 8) ∈ ({1, 4, 7} : Finset ℕ) := by decide
    exact fun {x y} => h x y
  loopless := ⟨by decide⟩

instance G8Dec : DecidableRel G8.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

