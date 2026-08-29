import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Matrix Equiv Finset

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Counting form of the permanent (membership in `#P`).**
The permanent of a `0/1` matrix is the number of permutations `σ` all of whose entries
`A (σ i) i` equal `1`, i.e. the number of perfect matchings of the bipartite graph
described by `A`. -/

theorem rowFun_injective (A : Matrix (Fin n) (Fin n) ℕ) {τ : Perm (Vtx n K)} (hτ : Valid A τ) :
    Function.Injective (rowFun τ) := by
  intro c c' h
  have e1 := valid_inr A hτ c
  have e2 := valid_inr A hτ c'
  rw [h] at e1
  have hmid := τ.injective (e1.trans e2.symm)
  have : (rowFun τ c, c, colFun τ c) = (rowFun τ c', c', colFun τ c') := by
    simpa using hmid
  simpa using congrArg (fun p : Mid n K => p.2.1) this

end Gadget

end CS

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

