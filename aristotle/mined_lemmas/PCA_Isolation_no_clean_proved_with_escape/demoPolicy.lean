/-!
# No Clean Proved With Escape
Category: Proof-Carrying Apps
Target: PCA.Isolation.no_clean_proved_with_escape
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Isolation

/-- Capabilities an app may exercise (e.g. file handles, sockets, syscalls). -/
abbrev Cap : Type := Nat

/-- A sandbox policy is the predicate describing which capabilities the
isolation engine permits. -/
abbrev Policy : Type := Cap → Prop

/-- A minimal app language for the isolation engine: capability uses, sequencing,
resolved conditionals, and bounded loops. -/
inductive Prog : Type
  | skip : Prog
  | use : Cap → Prog
  | seq : Prog → Prog → Prog
  | ite : Bool → Prog → Prog → Prog
  | loop : Nat → Prog → Prog
  deriving DecidableEq

namespace Prog

/-- `rep n t` is `t` repeated `n` times, the trace of a bounded loop body. -/

def demoPolicy : Policy := fun c => c = 0 ∨ c = 1

/-- A concrete app that the engine certifies. -/
example : ProvedClean demoPolicy (.seq (.use 0) (.loop 3 (.use 1))) :=
  Safe.seq (Safe.use (Or.inl rfl)) (Safe.loop_succ (Safe.use (Or.inr rfl)))

/-- A concrete app that escapes the sandbox. -/
example : Escapes demoPolicy (.seq (.use 0) (.use 2)) :=
  ⟨2, by simp, by simp [demoPolicy]⟩

/-- Hence that app is not certified by the engine. -/
example : ¬ ProvedClean demoPolicy (.seq (.use 0) (.use 2)) := fun h =>
  no_clean_proved_with_escape _ _ ⟨h, ⟨2, by simp, by simp [demoPolicy]⟩⟩

end PCA.Isolation

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

