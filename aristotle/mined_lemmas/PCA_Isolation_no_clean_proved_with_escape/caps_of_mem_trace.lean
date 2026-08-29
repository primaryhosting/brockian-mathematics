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

theorem caps_of_mem_trace {p : Prog Cap} {t : List Cap} (h : Runs p t) :
    ∀ c ∈ t, caps p c := by
  induction h with
  | nop => simp
  | use c => intro d hd; simp at hd; exact hd
  | seq _ _ ih₁ ih₂ =>
      intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · exact Or.inl (ih₁ c hc)
      · exact Or.inr (ih₂ c hc)
  | branchL _ ih => exact fun c hc => Or.inl (ih c hc)
  | branchR _ ih => exact fun c hc => Or.inr (ih c hc)
  | loopZero => simp
  | loopStep _ _ ih₁ ih₂ =>
      intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · exact ih₁ c hc
      · exact ih₂ c hc

/-- Every app has at least one possible run-time trace. -/
