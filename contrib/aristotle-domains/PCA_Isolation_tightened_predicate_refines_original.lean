/-!
# Tightened Predicate Refines Original
Category: Proof-Carrying Apps
Target: PCA.Isolation.tightened_predicate_refines_original
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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

/-!
# A formal model of a predicate-based isolation engine

This file develops a small but complete formal model of the *isolation engine* underlying a
predicate/component analysis (`PCA`): an engine observes a state space `σ`, carries a finite list
of *isolation guards* (side conditions that the engine may additionally assume/enforce), and
*tightens* a user-supplied predicate by conjoining those guards.

The central correctness statement is
`PCA.Isolation.tightened_predicate_refines_original`: tightening is always a *refinement*, i.e.
every state admitted by the tightened predicate is admitted by the original one.  This is the
soundness half of the model.  The completeness half
(`PCA.Isolation.original_refines_tightened_of_guards_valid`) says that when the guards are already
implied by the original predicate, the tightened predicate admits exactly as much as the original,
so tightening loses no information.

Beyond the two halves we record the algebraic structure of tightening (monotonicity,
idempotence, greatest-lower-bound characterisation), its interaction with the transition relation
(inductive invariants and reachability), and the fact that the engine never isolates a state
"for no reason".
-/

namespace PCA
namespace Isolation

variable {σ : Type*}

/-- A predicate over the engine's state space: the engine's model of a set of states. -/
def Pred (σ : Type*) : Type _ := σ → Prop

/-- `p` *refines* `q` when every state admitted by `p` is admitted by `q`. -/
def Refines (p q : Pred σ) : Prop := ∀ s : σ, p s → q s

/-- Two predicates are *equivalent* when they refine each other. -/
def Equiv (p q : Pred σ) : Prop := Refines p q ∧ Refines q p

/-- An isolation engine: a transition relation on states together with a finite list of
isolation guards that the engine enforces. -/
structure Engine (σ : Type*) where
  /-- one-step transition relation of the modelled system -/
  step : σ → σ → Prop
  /-- the guards the engine enforces when isolating -/
  guards : List (Pred σ)

/-- The conjunction of all guards of an engine. -/
def Engine.guardAll (E : Engine σ) : Pred σ := fun s => ∀ g ∈ E.guards, g s

/-- The engine's *tightening* of a predicate: the original predicate conjoined with all guards. -/
def Engine.tighten (E : Engine σ) (P : Pred σ) : Pred σ := fun s => P s ∧ E.guardAll s

/-- The guards are *valid* for `P` when every state admitted by `P` already satisfies them. -/
def Engine.GuardsValid (E : Engine σ) (P : Pred σ) : Prop := Refines P E.guardAll

/-- `P` is an inductive invariant of the engine's transition relation. -/
def Engine.Inductive (E : Engine σ) (P : Pred σ) : Prop :=
  ∀ s t : σ, P s → E.step s t → P t

/-- Reachability along the engine's transition relation. -/
inductive Engine.Reach (E : Engine σ) (P : Pred σ) : σ → Prop
  | base {s : σ} : P s → E.Reach P s
  | step {s t : σ} : E.Reach P s → E.step s t → E.Reach P t

/-! ## Basic order-theoretic facts about refinement -/

theorem Refines.refl (p : Pred σ) : Refines p p := fun _ h => h

theorem Refines.trans {p q r : Pred σ} (hpq : Refines p q) (hqr : Refines q r) : Refines p r :=
  fun s hs => hqr s (hpq s hs)

theorem Refines.antisymm {p q : Pred σ} (hpq : Refines p q) (hqp : Refines q p) : p = q := by
  funext s
  exact propext ⟨hpq s, hqp s⟩

theorem Equiv.eq {p q : Pred σ} (h : Equiv p q) : p = q :=
  Refines.antisymm h.1 h.2

/-! ## Soundness: tightening refines the original predicate -/

/-- **Soundness of the isolation engine.**  The predicate produced by tightening always refines
the predicate it was produced from: isolating can only shrink the admitted state set, never
enlarge it.  Consequently the engine never admits a state that the original model rejects. -/
theorem tightened_predicate_refines_original (E : Engine σ) (P : Pred σ) :
    Refines (E.tighten P) P := by
  intro s hs
  exact hs.1

/-- Tightening also refines the conjunction of the guards. -/
theorem tightened_predicate_refines_guards (E : Engine σ) (P : Pred σ) :
    Refines (E.tighten P) E.guardAll := by
  intro s hs
  exact hs.2

/-- A state admitted by the tightened predicate satisfies every individual guard. -/
theorem guard_of_tightened (E : Engine σ) (P : Pred σ) {s : σ} (hs : E.tighten P s)
    {g : Pred σ} (hg : g ∈ E.guards) : g s :=
  hs.2 g hg

/-! ## Completeness: nothing is lost when the guards are valid -/

/-- **Completeness of the isolation engine.**  If the guards are valid for `P` — i.e. every state
admitted by `P` already satisfies them — then the original predicate refines the tightened one. -/
theorem original_refines_tightened_of_guards_valid (E : Engine σ) (P : Pred σ)
    (h : E.GuardsValid P) : Refines P (E.tighten P) := by
  intro s hs
  exact ⟨hs, h s hs⟩

/-- Soundness and completeness combined: with valid guards, tightening is information preserving. -/
theorem tighten_equiv_of_guards_valid (E : Engine σ) (P : Pred σ) (h : E.GuardsValid P) :
    Equiv (E.tighten P) P :=
  ⟨tightened_predicate_refines_original E P, original_refines_tightened_of_guards_valid E P h⟩

/-- With valid guards, tightening does not change the predicate at all. -/
theorem tighten_eq_of_guards_valid (E : Engine σ) (P : Pred σ) (h : E.GuardsValid P) :
    E.tighten P = P :=
  Equiv.eq (tighten_equiv_of_guards_valid E P h)

/-- Conversely, if tightening loses nothing then the guards were valid: validity of the guards is
*exactly* the condition under which the engine is complete. -/
theorem guards_valid_of_original_refines_tightened (E : Engine σ) (P : Pred σ)
    (h : Refines P (E.tighten P)) : E.GuardsValid P := by
  intro s hs
  exact (h s hs).2

/-- Completeness is equivalent to validity of the guards. -/
theorem guards_valid_iff_complete (E : Engine σ) (P : Pred σ) :
    E.GuardsValid P ↔ Refines P (E.tighten P) :=
  ⟨original_refines_tightened_of_guards_valid E P, guards_valid_of_original_refines_tightened E P⟩

/-! ## The engine never isolates a state without a reason -/

/-- Every state that the engine rejects but the original model accepts violates a *named* guard;
the engine can always exhibit a witness for the isolation it performs. -/
theorem exists_violated_guard_of_not_tightened (E : Engine σ) (P : Pred σ) {s : σ}
    (hP : P s) (h : ¬ E.tighten P s) : ∃ g ∈ E.guards, ¬ g s := by
  by_contra hcon
  push_neg at hcon
  exact h ⟨hP, fun g hg => hcon g hg⟩

/-- An engine with no guards performs no isolation whatsoever. -/
theorem tighten_of_guards_nil (E : Engine σ) (P : Pred σ) (h : E.guards = []) :
    E.tighten P = P := by
  apply tighten_eq_of_guards_valid
  intro s _ g hg
  rw [h] at hg
  exact absurd hg (List.not_mem_nil)

/-! ## Algebraic structure of tightening -/

/-- Tightening is monotone in the predicate it is applied to. -/
theorem tighten_mono (E : Engine σ) {P Q : Pred σ} (h : Refines P Q) :
    Refines (E.tighten P) (E.tighten Q) := by
  intro s hs
  exact ⟨h s hs.1, hs.2⟩

/-- Tightening is idempotent: re-running the engine isolates nothing new. -/
theorem tighten_idem (E : Engine σ) (P : Pred σ) : E.tighten (E.tighten P) = E.tighten P := by
  funext s
  exact propext ⟨fun h => h.1, fun h => ⟨h, h.2⟩⟩

/-- Tightening is the *greatest* predicate that refines both the original predicate and the
guards: it is the exact (most permissive sound) isolation. -/
theorem tighten_greatest (E : Engine σ) (P R : Pred σ) (hP : Refines R P)
    (hG : Refines R E.guardAll) : Refines R (E.tighten P) :=
  fun s hs => ⟨hP s hs, hG s hs⟩

/-- Characterisation of the tightened predicate by a universal property. -/
theorem refines_tighten_iff (E : Engine σ) (P R : Pred σ) :
    Refines R (E.tighten P) ↔ Refines R P ∧ Refines R E.guardAll :=
  ⟨fun h => ⟨fun s hs => (h s hs).1, fun s hs => (h s hs).2⟩,
   fun h => tighten_greatest E P R h.1 h.2⟩

/-- Adding a guard tightens further: the extended engine's output refines the original one's. -/
theorem tighten_append_refines (step : σ → σ → Prop) (gs hs' : List (Pred σ)) (P : Pred σ) :
    Refines (Engine.tighten ⟨step, gs ++ hs'⟩ P) (Engine.tighten ⟨step, gs⟩ P) := by
  intro s h
  refine ⟨h.1, fun g hg => h.2 g ?_⟩
  exact List.mem_append_left _ hg

/-! ## Interaction with the transition relation -/

/-- If both the original predicate and the guard conjunction are inductive invariants, so is the
tightened predicate. -/
theorem tighten_inductive (E : Engine σ) (P : Pred σ) (hP : E.Inductive P)
    (hG : E.Inductive E.guardAll) : E.Inductive (E.tighten P) := by
  intro s t hs hst
  exact ⟨hP s t hs.1 hst, hG s t hs.2 hst⟩

/-- Every state reachable from a predicate satisfying an inductive invariant still satisfies it. -/
theorem reach_of_inductive (E : Engine σ) (P : Pred σ) (hP : E.Inductive P) {s : σ}
    (h : E.Reach P s) : P s := by
  induction h with
  | base hs => exact hs
  | step _ hst ih => exact hP _ _ ih hst

/-- **Trace-level soundness.**  Every state reachable from the *tightened* predicate is reachable
from the original one: isolation never invents behaviour. -/
theorem reach_tighten_refines_reach (E : Engine σ) (P : Pred σ) {s : σ}
    (h : E.Reach (E.tighten P) s) : E.Reach P s := by
  induction h with
  | base hs => exact Engine.Reach.base hs.1
  | step _ hst ih => exact Engine.Reach.step ih hst
/-- Trace-level soundness, phrased as a refinement of reachability predicates. -/
theorem reach_tighten_refines (E : Engine σ) (P : Pred σ) :
    Refines (fun s => E.Reach (E.tighten P) s) (fun s => E.Reach P s) :=
  fun _ h => reach_tighten_refines_reach E P h

/-- **Trace-level completeness.**  With valid guards, the tightened predicate reaches exactly the
states the original predicate reaches. -/
theorem reach_tighten_eq_of_guards_valid (E : Engine σ) (P : Pred σ) (h : E.GuardsValid P) :
    (fun s => E.Reach (E.tighten P) s) = (fun s => E.Reach P s) := by
  rw [tighten_eq_of_guards_valid E P h]

/-- **Verification soundness.**  If the tightened predicate is an inductive invariant and every
tightened state is safe, then all states reachable from the tightened predicate are safe: a proof
carried out by the isolation engine transfers to the modelled system. -/
theorem safe_of_reach_tighten (E : Engine σ) (P Safe : Pred σ)
    (hind : E.Inductive (E.tighten P)) (hsafe : Refines (E.tighten P) Safe) {s : σ}
    (hs : E.Reach (E.tighten P) s) : Safe s :=
  hsafe s (reach_of_inductive E (E.tighten P) hind hs)

end Isolation
end PCA

