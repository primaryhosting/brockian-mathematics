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
# Polya Isomer Count
Category: Chemistry
Target: Chem.polya_isomer_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MulAction

namespace Chem

attribute [local instance] arrowAction

variable {G P C : Type*} [Group G] [MulAction G P]

/-- The subgroup of symmetries that leave a given substitution pattern (colouring) `f`
unchanged pointwise, i.e. `f (h • p) = f p` for all positions `p`. -/

def invariance (f : P → C) : Subgroup G where
  carrier := {h : G | ∀ p : P, f (h • p) = f p}
  mul_mem' := by
    intro a b ha hb p
    simp only [Set.mem_setOf_eq] at ha hb
    rw [mul_smul, ha, hb]
  one_mem' := by intro p; simp
  inv_mem' := by
    intro a ha p
    simp only [Set.mem_setOf_eq] at ha ⊢
    have := ha (a⁻¹ • p)
    rw [smul_inv_smul] at this
    exact this.symm

