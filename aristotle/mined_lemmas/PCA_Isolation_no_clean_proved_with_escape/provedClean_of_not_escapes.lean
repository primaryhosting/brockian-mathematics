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

theorem provedClean_of_not_escapes (M : Machine State Effect) (allowed : Policy Effect)
    (h : ¬ Escapes M allowed) : ProvedClean M allowed :=
  ⟨{ Inv := Reach M
     init_mem := fun _ hs => Reach.init hs
     step_closed := fun _ _ _ hs hstep => Reach.step hs hstep
     effects_allowed := fun s e s' hs hstep =>
       Classical.byContradiction fun hbad => h ⟨s, e, s', hs, hstep, hbad⟩ }⟩

/-- Soundness and completeness combined: being proved clean is *equivalent* to not
escaping. -/
