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
# Tightened Predicate Refines Original
Category: Proof-Carrying Apps
Target: PCA.Isolation.tightened_predicate_refines_original
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Isolation

/-- A state of the isolated component: the capabilities it currently holds
and the amount of fuel (resource budget) it may still consume. -/
structure State where
  /-- Capabilities held by the component, identified by natural numbers. -/
  caps : List Nat
  /-- Remaining resource budget. -/
  fuel : Nat

/-- A predicate of the isolation engine's model: a property of states. -/
structure Predicate where
  /-- The underlying property of states. -/
  holds : State → Prop

/-- `Refines p q` says that `p` is at least as strong as `q`: every state admitted
by `p` is admitted by `q`. -/
def Refines (p q : Predicate) : Prop := ∀ s : State, p.holds s → q.holds s

theorem refines_refl (p : Predicate) : Refines p p := fun _ h => h

theorem refines_trans {p q r : Predicate} (hpq : Refines p q) (hqr : Refines q r) :
    Refines p r := fun s h => hqr s (hpq s h)

/-- The tightenings that the isolation engine may apply to a predicate. -/
inductive Tightening where
  /-- Do not tighten at all. -/
  | skip : Tightening
  /-- Conjoin an arbitrary extra guard. -/
  | guard : (State → Prop) → Tightening
  /-- Require the held capabilities to lie inside an allowed list. -/
  | capBound : List Nat → Tightening
  /-- Require the remaining fuel to be within a bound. -/
  | fuelBound : Nat → Tightening
  /-- Apply two tightenings in sequence. -/
  | seq : Tightening → Tightening → Tightening

/-- Applying a tightening to a predicate. -/
def Tightening.apply : Tightening → Predicate → Predicate
  | .skip, p => p
  | .guard g, p => ⟨fun s => p.holds s ∧ g s⟩
  | .capBound A, p => ⟨fun s => p.holds s ∧ s.caps ⊆ A⟩
  | .fuelBound n, p => ⟨fun s => p.holds s ∧ s.fuel ≤ n⟩
  | .seq t₁ t₂, p => t₂.apply (t₁.apply p)

/-- **Soundness of tightening.** Whatever tightening the isolation engine applies,
the resulting predicate refines the original one: every state accepted by the
tightened predicate is already accepted by the original predicate. -/
theorem tightened_predicate_refines_original (t : Tightening) (p : Predicate) :
    Refines (t.apply p) p := by
  induction t generalizing p with
  | skip => exact refines_refl p
  | guard g => exact fun _ h => h.1
  | capBound A => exact fun _ h => h.1
  | fuelBound n => exact fun _ h => h.1
  | seq t₁ t₂ ih₁ ih₂ => exact refines_trans (ih₂ (t₁.apply p)) (ih₁ p)

/-- Tightening is monotone with respect to refinement. -/
theorem tightening_mono (t : Tightening) : ∀ {p q : Predicate}, Refines p q →
    Refines (t.apply p) (t.apply q) := by
  induction t with
  | skip => exact fun h => h
  | guard g => exact fun h s hs => ⟨h s hs.1, hs.2⟩
  | capBound A => exact fun h s hs => ⟨h s hs.1, hs.2⟩
  | fuelBound n => exact fun h s hs => ⟨h s hs.1, hs.2⟩
  | seq t₁ t₂ ih₁ ih₂ => exact fun h => ih₂ (ih₁ h)

/-- **No loss on compliant states.** A state accepted by the original predicate is
still accepted after adding a guard, provided it satisfies that guard; so tightening
only removes states that violate the newly imposed constraint. -/
theorem tightened_holds_of_guard (p : Predicate) (s : State) (g : State → Prop)
    (hp : p.holds s) (hg : g s) : ((Tightening.guard g).apply p).holds s :=
  ⟨hp, hg⟩

end PCA.Isolation

