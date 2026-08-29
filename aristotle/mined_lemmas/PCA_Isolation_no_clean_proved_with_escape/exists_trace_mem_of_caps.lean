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

theorem exists_trace_mem_of_caps {p : Prog Cap} {c : Cap} (h : caps p c) :
    ∃ t, Runs p t ∧ c ∈ t := by
  induction p with
  | nop => exact absurd h (by simp [caps])
  | use d => exact ⟨[d], Runs.use d, by simp [show c = d from h]⟩
  | seq p q ihp ihq =>
      rcases h with h | h
      · obtain ⟨t, ht, hc⟩ := ihp h
        obtain ⟨t', ht'⟩ := exists_trace q
        exact ⟨t ++ t', Runs.seq ht ht', by simp [hc]⟩
      · obtain ⟨t, ht, hc⟩ := ihq h
        obtain ⟨t', ht'⟩ := exists_trace p
        exact ⟨t' ++ t, Runs.seq ht' ht, by simp [hc]⟩
  | branch p q ihp ihq =>
      rcases h with h | h
      · obtain ⟨t, ht, hc⟩ := ihp h
        exact ⟨t, Runs.branchL ht, hc⟩
      · obtain ⟨t, ht, hc⟩ := ihq h
        exact ⟨t, Runs.branchR ht, hc⟩
  | loop p ihp =>
      obtain ⟨t, ht, hc⟩ := ihp h
      exact ⟨t ++ [], Runs.loopStep ht Runs.loopZero, by simp [hc]⟩

/-- **Main theorem.** No app is both proved clean by the isolation engine and able to
escape its sandbox: the certificate check is sound. -/
