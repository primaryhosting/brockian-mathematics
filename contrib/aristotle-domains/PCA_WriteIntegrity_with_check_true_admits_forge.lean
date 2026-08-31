/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.with_check_true_admits_forge
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
# A formal model of the write-integrity isolation engine (`PCA`)

This file develops a small, self-contained operational model of an *isolation engine*
that mediates writes of principals (subjects) to resources (objects), and proves the
soundness / completeness statements for the reference monitor, together with the
"necessity" statement that a degenerate check (one that always returns `true`) admits
a forgery.

The integrity policy is the classical *no write up* rule: a subject may write an object
only if the subject's integrity level dominates the integrity level required by the object.

Main results:

* `PCA.WriteIntegrity.refCheck_sound` : the reference check only lets authorized writes through.
* `PCA.WriteIntegrity.refCheck_no_forge` : running the engine with the reference check never
  produces a forgery: any resource whose contents changed was written by an authorized write.
* `PCA.WriteIntegrity.refCheck_complete` : the reference check never blocks an authorized write;
  on authorized traces the mediated run agrees with the unmediated one.
* `PCA.WriteIntegrity.with_check_true_admits_forge` : the always-accepting check admits a forgery,
  so the check is load bearing.
-/

namespace PCA
namespace WriteIntegrity

/-- Principals (subjects) of the isolation engine. -/
abbrev Principal := ℕ

/-- Resources (objects) mediated by the isolation engine. -/
abbrev Resource := ℕ

/-- Values that can be stored in a resource. -/
abbrev Value := ℤ

/-- An environment assigns an integrity level to every principal and to every resource. -/
structure Env where
  /-- Integrity level of a principal. -/
  level : Principal → ℕ
  /-- Integrity level required in order to write a resource. -/
  required : Resource → ℕ

/-- A write request: principal `subj` asks to store `val` into resource `obj`. -/
structure Write where
  /-- The requesting principal. -/
  subj : Principal
  /-- The target resource. -/
  obj : Resource
  /-- The value to be written. -/
  val : Value

/-- The store: the current contents of every resource. -/
def Store := Resource → Value

/-- The write-integrity policy ("no write up"): `w` is authorized in `E` when the level of
the writing principal dominates the level required by the target resource. -/
def Authorized (E : Env) (w : Write) : Prop :=
  E.required w.obj ≤ E.level w.subj

instance (E : Env) (w : Write) : Decidable (Authorized E w) := by
  unfold Authorized; infer_instance

/-- A *check* is any boolean predicate the engine consults before performing a write. -/
abbrev Check := Env → Write → Bool

/-- The reference monitor's check: exactly the write-integrity policy. -/
def refCheck : Check := fun E w => decide (Authorized E w)

/-- The degenerate check that accepts everything. -/
def trueCheck : Check := fun _ _ => true

/-- Unmediated effect of a write on the store. -/
def applyWrite (st : Store) (w : Write) : Store :=
  Function.update st w.obj w.val

/-- One step of the engine: the write happens only if the check accepts it. -/
def step (chk : Check) (E : Env) (st : Store) (w : Write) : Store :=
  if chk E w then applyWrite st w else st

/-- Running the engine on a trace of write requests. -/
def run (chk : Check) (E : Env) (st : Store) (ws : List Write) : Store :=
  ws.foldl (step chk E) st

/-- Running the trace with no mediation at all. -/
def runAll (st : Store) (ws : List Write) : Store :=
  ws.foldl applyWrite st

/-- A *forgery* at the level of the store: some resource's contents changed even though no
write to that resource in the trace was authorized by the policy. -/
def Forged (chk : Check) (E : Env) (st : Store) (ws : List Write) : Prop :=
  ∃ r : Resource, run chk E st ws r ≠ st r ∧ ∀ w ∈ ws, w.obj = r → ¬ Authorized E w

@[simp] theorem run_nil (chk : Check) (E : Env) (st : Store) : run chk E st [] = st := rfl

@[simp] theorem run_cons (chk : Check) (E : Env) (st : Store) (w : Write) (ws : List Write) :
    run chk E st (w :: ws) = run chk E (step chk E st w) ws := rfl

@[simp] theorem runAll_nil (st : Store) : runAll st [] = st := rfl

@[simp] theorem runAll_cons (st : Store) (w : Write) (ws : List Write) :
    runAll st (w :: ws) = runAll (applyWrite st w) ws := rfl

/-- The reference check accepts only authorized writes. -/
theorem refCheck_sound {E : Env} {w : Write} (h : refCheck E w = true) : Authorized E w := by
  simpa [refCheck] using h

/-- The reference check accepts every authorized write. -/
theorem refCheck_accepts {E : Env} {w : Write} (h : Authorized E w) : refCheck E w = true := by
  simpa [refCheck] using h

/-- Any change to a resource must be caused by a write to that resource that the check accepted. -/
theorem exists_accepted_write_of_ne (chk : Check) (E : Env) :
    ∀ (ws : List Write) (st : Store) (r : Resource), run chk E st ws r ≠ st r →
      ∃ w ∈ ws, w.obj = r ∧ chk E w = true := by
  intro ws
  induction ws with
  | nil => intro st r h; simp at h
  | cons w ws ih =>
      intro st r h
      rw [run_cons] at h
      by_cases hr : run chk E (step chk E st w) ws r = step chk E st w r
      · -- the tail did not change `r`, so the head write must have
        rw [hr] at h
        by_cases hc : chk E w = true
        · refine ⟨w, List.mem_cons_self .., ?_, hc⟩
          by_contra hne
          apply h
          simp [step, hc, applyWrite, Function.update_of_ne (Ne.symm hne)]
        · exact absurd (by simp [step, hc]) h
      · obtain ⟨v, hv, hvr, hvc⟩ := ih (step chk E st w) r hr
        exact ⟨v, List.mem_cons_of_mem _ hv, hvr, hvc⟩

/-- **Soundness of the isolation engine.** With the reference check installed, the engine never
admits a forgery: whenever the contents of a resource change, some authorized write to that
resource occurred in the trace. -/
theorem refCheck_no_forge (E : Env) (st : Store) (ws : List Write) :
    ¬ Forged refCheck E st ws := by
  rintro ⟨r, hne, hall⟩
  obtain ⟨w, hw, hwr, hwc⟩ := exists_accepted_write_of_ne refCheck E ws st r hne
  exact hall w hw hwr (refCheck_sound hwc)

/-- **Completeness of the isolation engine.** The reference check never blocks an authorized
write: on a trace of authorized writes the mediated run coincides with the unmediated run. -/
theorem refCheck_complete (E : Env) :
    ∀ (ws : List Write) (st : Store), (∀ w ∈ ws, Authorized E w) →
      run refCheck E st ws = runAll st ws := by
  intro ws
  induction ws with
  | nil => intro st _; rfl
  | cons w ws ih =>
      intro st h
      have hw : Authorized E w := h w (List.mem_cons_self ..)
      rw [run_cons, runAll_cons, step, if_pos (refCheck_accepts hw)]
      exact ih _ fun v hv => h v (List.mem_cons_of_mem _ hv)

/-- **Characterization of the safe checks.** An arbitrary check admits a forgery *iff* it accepts
some unauthorized write. This is the exact soundness/completeness criterion for the isolation
engine's model: a check is forgery-free precisely when it refines the write-integrity policy. -/
theorem admits_forge_iff_accepts_unauthorized (chk : Check) :
    (∃ (E : Env) (st : Store) (ws : List Write), Forged chk E st ws) ↔
      ∃ (E : Env) (w : Write), chk E w = true ∧ ¬ Authorized E w := by
  constructor
  · rintro ⟨E, st, ws, r, hne, hall⟩
    obtain ⟨w, hw, hwr, hwc⟩ := exists_accepted_write_of_ne chk E ws st r hne
    exact ⟨E, w, hwc, hall w hw hwr⟩
  · rintro ⟨E, w, hwc, hwa⟩
    refine ⟨E, fun _ => w.val + 1, [w], w.obj, ?_, ?_⟩
    · simp [run, step, hwc, applyWrite, Function.update_self]
    · intro v hv _
      simp only [List.mem_singleton] at hv
      simpa [hv] using hwa

/-- **Necessity of the check.** The engine instantiated with the always-accepting check admits a
forgery: there is an environment, an initial store and a trace containing no authorized write to
the affected resource, yet the contents of that resource change. -/
theorem with_check_true_admits_forge :
    ∃ (E : Env) (st : Store) (ws : List Write), Forged trueCheck E st ws := by
  refine (admits_forge_iff_accepts_unauthorized trueCheck).mpr
    ⟨⟨fun _ => 0, fun _ => 1⟩, ⟨0, 0, 1⟩, rfl, ?_⟩
  simp [Authorized]

end WriteIntegrity
end PCA

#print axioms PCA.WriteIntegrity.with_check_true_admits_forge
#print axioms PCA.WriteIntegrity.refCheck_no_forge
#print axioms PCA.WriteIntegrity.refCheck_complete

