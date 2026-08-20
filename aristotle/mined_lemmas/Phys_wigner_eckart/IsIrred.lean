/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Statement: Matrix elements of tensor operators factor into a Clebsch–Gordan × reduced element (Wigner–Eckart).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

open TensorProduct

variable {G : Type*} [Monoid G]

/-- `f` intertwines the representations `ρ` and `σ`. -/

def IsIrred {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) : Prop :=
  Nontrivial V ∧
    ∀ S : Submodule ℂ V, (∀ (g : G), ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤

/-- **Schur's lemma** (over `ℂ`): a self-intertwiner of a finite-dimensional irreducible
complex representation is a scalar. -/
