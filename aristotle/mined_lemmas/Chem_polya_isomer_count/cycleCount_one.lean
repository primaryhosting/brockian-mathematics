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

lemma cycleCount_one : cycleCount P (1 : G) = Nat.card P := by
  refine Nat.card_congr ?_
  refine Equiv.ofBijective (Quotient.lift id ?_) ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨h, rfl⟩ := hab
    obtain ⟨k, hk⟩ := h.2
    have hh : (h : G) = 1 := by simpa using hk.symm
    show (h : G) • b = b
    rw [hh, one_smul]
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | h a =>
      induction y using Quotient.inductionOn with
      | h b =>
        have hab : a = b := hxy
        rw [hab]
  · intro p
    exact ⟨Quotient.mk _ p, rfl⟩

/-- Substitution patterns fixed by a symmetry `g` are exactly the colourings that are constant
on the cycles of `g`, so they correspond to functions on the set of cycles. -/
