/-
# No Clean Proved With Escape
Category: Proof-Carrying Apps
Target: PCA.Isolation.no_clean_proved_with_escape
Verification: pending
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

namespace PCA.Isolation

/-! ## The isolation model

We model a *proof-carrying app* as a program running on an **unchecked** runtime:
the runtime performs every effect the program asks for, without consulting the
capability set.  Isolation is therefore guaranteed only by the static
certificate checker, together with the requirement that the app be *clean*
(contain no ambient-authority escape hatch).
-/

/-- A capability (an abstract permission token). -/
abbrev Cap := ℕ

/-- Instructions of the app language. -/
inductive Instr where
  /-- Perform an effect that requires capability `c`. -/
  | use : Cap → Instr
  /-- Escape hatch: grant capability `c` to the ambient capability set. -/
  | grant : Cap → Instr
  deriving DecidableEq

/-- An app: a sandbox policy (the capabilities the app is entitled to) and its code. -/
structure App where
  policy : Finset Cap
  prog : List Instr

/-- Runtime state: the current capability set, the code left to run, and the
log of effects already performed. -/
structure State where
  caps : Finset Cap
  prog : List Instr
  log : List Cap

/-- Small-step operational semantics.  Note that `use` is *not* guarded by the
capability set: the runtime is unchecked. -/
inductive Step : State → State → Prop where
  | use (caps : Finset Cap) (c : Cap) (p : List Instr) (log : List Cap) :
      Step ⟨caps, Instr.use c :: p, log⟩ ⟨caps, p, c :: log⟩
  | grant (caps : Finset Cap) (c : Cap) (p : List Instr) (log : List Cap) :
      Step ⟨caps, Instr.grant c :: p, log⟩ ⟨insert c caps, p, log⟩

/-- Reachability in the operational semantics. -/

theorem exists_reach_log_of_mem_use {caps : Finset Cap} {p : List Instr}
    {log : List Cap} {c : Cap} (h : Instr.use c ∈ p) :
    ∃ s : State, Reach ⟨caps, p, log⟩ s ∧ c ∈ s.log := by
  induction p generalizing caps log with
  | nil => exact absurd h (List.not_mem_nil)
  | cons i rest ih =>
      cases i with
      | use d =>
          by_cases hd : d = c
          · subst hd
            exact ⟨⟨caps, rest, d :: log⟩,
              Relation.ReflTransGen.single (Step.use caps d rest log),
              List.mem_cons_self ..⟩
          · have hmem : Instr.use c ∈ rest := by
              rcases List.mem_cons.mp h with h' | h'
              · exact absurd (by simpa using h'.symm) hd
              · exact h'
            obtain ⟨s, hs, hcs⟩ := ih (caps := caps) (log := d :: log) hmem
            exact ⟨s, Relation.ReflTransGen.head (Step.use caps d rest log) hs, hcs⟩
      | grant d =>
          have hmem : Instr.use c ∈ rest := by
            rcases List.mem_cons.mp h with h' | h'
            · exact absurd h' (by simp)
            · exact h'
          obtain ⟨s, hs, hcs⟩ := ih (caps := insert d caps) (log := log) hmem
          exact ⟨s, Relation.ReflTransGen.head (Step.grant caps d rest log) hs, hcs⟩

