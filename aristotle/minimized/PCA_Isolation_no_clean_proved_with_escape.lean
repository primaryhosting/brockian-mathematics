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
# No Clean Proved With Escape
Category: Proof-Carrying Apps
Target: PCA.Isolation.no_clean_proved_with_escape
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA
namespace Isolation

universe u v

/-- An abstract model of a sandboxed application: a labelled transition system whose
labels are the observable effects (syscalls, resource accesses, ...) that the isolation
engine mediates. -/
structure Machine (State : Type u) (Effect : Type v) where
  /-- The set of admissible initial states. -/
  init : State → Prop
  /-- `step s e s'` : from state `s` the app may perform effect `e` and move to `s'`. -/
  step : State → Effect → State → Prop

variable {State : Type u} {Effect : Type v}

/-- A sandbox policy: the predicate holding of exactly the permitted effects. -/
abbrev Policy (Effect : Type v) : Type v := Effect → Prop

/-- States reachable from an initial state by finitely many steps. -/
inductive Reach (M : Machine State Effect) : State → Prop
  | init {s : State} (h : M.init s) : Reach M s
  | step {s : State} {e : Effect} {s' : State}
      (hs : Reach M s) (hstep : M.step s e s') : Reach M s'

/-- The app *escapes* the sandbox described by `allowed` if some reachable state can
perform an effect outside the policy. -/

def Escapes (M : Machine State Effect) (allowed : Policy Effect) : Prop :=
  ∃ s e s', Reach M s ∧ M.step s e s' ∧ ¬ allowed e

/-- A proof certificate carried by the app: an inductive invariant witnessing that every
effect the app can ever perform lies inside the policy. This is exactly the artifact the
isolation engine's checker validates. -/
structure Certificate (M : Machine State Effect) (allowed : Policy Effect) where
  /-- The claimed inductive invariant. -/
  Inv : State → Prop
  /-- The invariant holds initially. -/
  init_mem : ∀ s, M.init s → Inv s
  /-- The invariant is preserved by every step. -/
  step_closed : ∀ s e s', Inv s → M.step s e s' → Inv s'
  /-- Every effect enabled in an invariant state is permitted by the policy. -/
  effects_allowed : ∀ s e s', Inv s → M.step s e s' → allowed e

/-- An app is *proved clean* when it carries a valid certificate. -/

def ProvedClean (M : Machine State Effect) (allowed : Policy Effect) : Prop :=
  Nonempty (Certificate M allowed)

/-- A valid certificate over-approximates reachability. -/

theorem Certificate.reach_imp {M : Machine State Effect} {allowed : Policy Effect}
    (C : Certificate M allowed) : ∀ {s : State}, Reach M s → C.Inv s := by
  intro s hs
  induction hs with
  | init h => exact C.init_mem _ h
  | step _ hstep ih => exact C.step_closed _ _ _ ih hstep

/-- **Soundness of the isolation engine.** No app is simultaneously proved clean and able
to escape its sandbox. -/

theorem no_clean_proved_with_escape (M : Machine State Effect) (allowed : Policy Effect) :
    ¬ (ProvedClean M allowed ∧ Escapes M allowed) := by
  rintro ⟨⟨C⟩, s, e, s', hreach, hstep, hbad⟩
  exact hbad (C.effects_allowed s e s' (C.reach_imp hreach) hstep)

/-- **Completeness of the certificate discipline.** If an app cannot escape, then the
reachability predicate itself is a valid certificate, so the app is provably clean. -/
