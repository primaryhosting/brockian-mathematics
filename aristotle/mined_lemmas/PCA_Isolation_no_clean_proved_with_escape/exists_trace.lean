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

namespace PCA.Isolation

universe u

variable {Cap : Type u}

/-- A sandboxed app, modelled as a structured program over a type of capabilities
(system calls / privileged operations). -/
inductive Prog (Cap : Type u) : Type u
  /-- Do nothing. -/
  | nop : Prog Cap
  /-- Exercise capability `c`. -/
  | use (c : Cap) : Prog Cap
  /-- Sequential composition. -/
  | seq (p q : Prog Cap) : Prog Cap
  /-- Nondeterministic branch (either arm may be taken at run time). -/
  | branch (p q : Prog Cap) : Prog Cap
  /-- Loop, executed an arbitrary finite number of times. -/
  | loop (p : Prog Cap) : Prog Cap

/-- Operational semantics: `Runs p t` says that `t` is a possible run-time trace of
capability uses of the app `p`. -/
inductive Runs : Prog Cap → List Cap → Prop
  | nop : Runs .nop []
  | use (c : Cap) : Runs (.use c) [c]
  | seq {p q : Prog Cap} {t₁ t₂ : List Cap} :
      Runs p t₁ → Runs q t₂ → Runs (.seq p q) (t₁ ++ t₂)
  | branchL {p q : Prog Cap} {t : List Cap} : Runs p t → Runs (.branch p q) t
  | branchR {p q : Prog Cap} {t : List Cap} : Runs q t → Runs (.branch p q) t
  | loopZero {p : Prog Cap} : Runs (.loop p) []
  | loopStep {p : Prog Cap} {t₁ t₂ : List Cap} :
      Runs p t₁ → Runs (.loop p) t₂ → Runs (.loop p) (t₁ ++ t₂)

/-- The isolation engine's static capability analysis: `caps p c` holds when the app `p`
could possibly exercise the capability `c`. -/

theorem exists_trace (p : Prog Cap) : ∃ t, Runs p t := by
  induction p with
  | nop => exact ⟨[], Runs.nop⟩
  | use c => exact ⟨[c], Runs.use c⟩
  | seq p q ihp ihq =>
      obtain ⟨t₁, h₁⟩ := ihp
      obtain ⟨t₂, h₂⟩ := ihq
      exact ⟨t₁ ++ t₂, Runs.seq h₁ h₂⟩
  | branch p q ihp _ =>
      obtain ⟨t, h⟩ := ihp
      exact ⟨t, Runs.branchL h⟩
  | loop p _ => exact ⟨[], Runs.loopZero⟩

/-- Completeness of the static analysis: every statically predicted capability really is
exercised on some run-time trace. -/
