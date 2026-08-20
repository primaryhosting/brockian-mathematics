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

noncomputable def fixedByEquivCycleFunctions (g : G) :
    (fixedBy (P → C) g) ≃ (orbitRel.Quotient (Subgroup.zpowers g) P → C) where
  toFun := fun f => by
    refine Quotient.lift f.1 ?_
    intro p q hpq
    obtain ⟨h, rfl⟩ := (orbitRel_apply.mp hpq)
    have hg : g ∈ (invariance f.1 : Subgroup G) := by
      intro p
      have h1 : f.1 (g⁻¹ • (g • p)) = f.1 (g • p) := congrFun f.2 (g • p)
      rw [inv_smul_smul] at h1
      exact h1.symm
    have : (h : G) ∈ (invariance f.1 : Subgroup G) := by
      have hle : Subgroup.zpowers g ≤ invariance f.1 := by
        rw [Subgroup.zpowers_le]
        exact hg
      exact hle h.2
    exact this q
  invFun := fun F => by
    refine ⟨fun p => F (Quotient.mk _ p), ?_⟩
    funext p
    show F (Quotient.mk _ (g⁻¹ • p)) = F (Quotient.mk _ p)
    have hq : (Quotient.mk _ (g⁻¹ • p) : orbitRel.Quotient (Subgroup.zpowers g) P)
        = Quotient.mk _ p := by
      apply Quotient.sound
      show g⁻¹ • p ∈ orbit (Subgroup.zpowers g) p
      exact ⟨⟨g⁻¹, inv_mem (Subgroup.mem_zpowers g)⟩, rfl⟩
    exact congrArg F hq
  left_inv := by intro f; ext p; rfl
  right_inv := by
    intro F
    funext x
    induction x using Quotient.inductionOn with
    | h p => rfl

