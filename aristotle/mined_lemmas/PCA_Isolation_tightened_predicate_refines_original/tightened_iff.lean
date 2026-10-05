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

/-
# Tightened Predicate Refines Original
Category: Proof-Carrying Apps
Target: PCA.Isolation.tightened_predicate_refines_original
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Isolation

/-- An access request handled by the isolation engine: a subject touching an
object, either for writing (`isWrite = true`) or for reading. -/
structure Access where
  subject : Nat
  object : Nat
  isWrite : Bool
deriving DecidableEq, Repr

/-- The state of the isolation engine: the number of registered subjects and
objects, together with the security level assigned to each. -/
structure Engine where
  subjects : Nat
  objects : Nat
  subjectLevel : Nat → Nat
  objectLevel : Nat → Nat

variable (E : Engine) (a : Access)

/-- The access stays inside the part of the world the engine actually models:
both the subject and the object are registered. -/

theorem tightened_iff :
    tightened E a ↔
      original E a ∧ inDomain E a ∧
        (a.isWrite = true → E.objectLevel a.object ≤ E.subjectLevel a.subject) := by
  unfold tightened original inDomain
  by_cases hw : a.isWrite = true
  · simp only [hw, if_true, forall_true_left]
    constructor
    · rintro ⟨hd, h⟩; exact ⟨h.le, hd, h.ge⟩
    · rintro ⟨h1, hd, h2⟩; exact ⟨hd, le_antisymm h1 h2⟩
  · simp only [Bool.not_eq_true] at hw
    simp only [hw, Bool.false_eq_true, if_false, false_implies, and_true]
    tauto

/-- The refinement is strict: there are accesses the original predicate allows
but the tightened one rejects. -/
