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
def inDomain : Prop := a.subject < E.subjects ∧ a.object < E.objects

/-- The original (Bell–LaPadula style) authorization predicate: no read up,
no write down. -/
def original : Prop :=
  if a.isWrite then E.subjectLevel a.subject ≤ E.objectLevel a.object
  else E.objectLevel a.object ≤ E.subjectLevel a.subject

/-- The tightened predicate used by the isolation engine: the access must be
in the engine's domain, reads still may not read up, and writes are only
allowed between *equal* levels (no write up either). -/
def tightened : Prop :=
  inDomain E a ∧
    (if a.isWrite then E.subjectLevel a.subject = E.objectLevel a.object
      else E.objectLevel a.object ≤ E.subjectLevel a.subject)

instance : Decidable (inDomain E a) := by unfold inDomain; infer_instance
instance : Decidable (original E a) := by unfold original; infer_instance
instance : Decidable (tightened E a) := by unfold tightened; infer_instance

/-- **Soundness of the tightening**: every access accepted by the tightened
predicate is accepted by the original one, i.e. the tightened predicate is a
refinement of the original. -/
theorem tightened_predicate_refines_original : tightened E a → original E a := by
  rintro ⟨-, h⟩
  unfold original
  by_cases hw : a.isWrite = true
  · simp only [hw, if_true] at h ⊢
    exact h.le
  · simp only [Bool.not_eq_true] at hw
    simp only [hw, Bool.false_eq_true, if_false] at h ⊢
    exact h

/-- Exact characterization of the tightening: it is the original predicate
conjoined with the domain check and the extra "no write up" restriction. -/
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
theorem tightened_strictly_stronger :
    ∃ (E : Engine) (a : Access), original E a ∧ ¬ tightened E a := by
  refine ⟨⟨1, 1, fun _ => 0, fun _ => 1⟩, ⟨0, 0, true⟩, ?_, ?_⟩
  · simp [original]
  · simp [tightened]

/-- Boolean version of `original`, for executable policy checking. -/
def originalB : Bool :=
  if a.isWrite then decide (E.subjectLevel a.subject ≤ E.objectLevel a.object)
  else decide (E.objectLevel a.object ≤ E.subjectLevel a.subject)

/-- Boolean version of `tightened`, for executable policy checking. -/
def tightenedB : Bool :=
  decide (a.subject < E.subjects) && decide (a.object < E.objects) &&
    (if a.isWrite then decide (E.subjectLevel a.subject = E.objectLevel a.object)
      else decide (E.objectLevel a.object ≤ E.subjectLevel a.subject))

theorem originalB_iff : originalB E a = true ↔ original E a := by
  unfold originalB original
  by_cases hw : a.isWrite <;> simp [hw]

theorem tightenedB_iff : tightenedB E a = true ↔ tightened E a := by
  unfold tightenedB tightened inDomain
  by_cases hw : a.isWrite <;> simp [hw, and_assoc]

/-- The executable checkers satisfy the same refinement. -/
theorem tightenedB_le_originalB : tightenedB E a = true → originalB E a = true := by
  intro h
  exact (originalB_iff E a).2
    (tightened_predicate_refines_original E a ((tightenedB_iff E a).1 h))

/-- A concrete engine, used for a finite decidable sanity check. -/
def demoEngine : Engine where
  subjects := 8
  objects := 8
  subjectLevel := fun s => s % 3
  objectLevel := fun o => o % 2

/-- Finite decidable instance of the refinement on `demoEngine`. -/
theorem demo_refines_check :
    ∀ s ∈ Finset.range 8, ∀ o ∈ Finset.range 8, ∀ w : Bool,
      tightenedB demoEngine ⟨s, o, w⟩ = true → originalB demoEngine ⟨s, o, w⟩ = true := by
  decide

end PCA.Isolation

#print axioms PCA.Isolation.tightened_predicate_refines_original
#print axioms PCA.Isolation.tightened_iff
#print axioms PCA.Isolation.demo_refines_check

