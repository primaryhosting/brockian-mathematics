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
def Reach : State → State → Prop := Relation.ReflTransGen Step

/-- Initial state of an app. -/
def init (a : App) : State := ⟨a.policy, a.prog, []⟩

/-- The static certificate checker: every `use` must be covered by the
capability set tracked at that program point. -/
def check (caps : Finset Cap) : List Instr → Bool
  | [] => true
  | Instr.use c :: rest => decide (c ∈ caps) && check caps rest
  | Instr.grant c :: rest => check (insert c caps) rest

/-- An app is *proved* when its certificate checks against its policy. -/
def Proved (a : App) : Prop := check a.policy a.prog = true

/-- A program is clean when it contains no ambient-authority escape hatch. -/
def CleanProg (p : List Instr) : Prop := ∀ c : Cap, Instr.grant c ∉ p

/-- An app is clean when its code is clean. -/
def Clean (a : App) : Prop := CleanProg a.prog

/-- An app *escapes* if some reachable state has logged an effect using a
capability outside its policy. -/
def Escapes (a : App) : Prop :=
  ∃ s : State, Reach (init a) s ∧ ∃ c : Cap, c ∈ s.log ∧ c ∉ a.policy

/-! ## Soundness -/

/-- The invariant maintained by clean, certified programs. -/
def Inv (policy : Finset Cap) (s : State) : Prop :=
  CleanProg s.prog ∧ check s.caps s.prog = true ∧ s.caps ⊆ policy ∧
    ∀ c ∈ s.log, c ∈ policy

theorem cleanProg_tail {i : Instr} {p : List Instr} (h : CleanProg (i :: p)) :
    CleanProg p := by
  intro c hc
  exact h c (List.mem_cons_of_mem i hc)

theorem inv_step {policy : Finset Cap} {s t : State} (hst : Step s t)
    (hs : Inv policy s) : Inv policy t := by
  obtain ⟨hclean, hchk, hcaps, hlog⟩ := hs
  cases hst with
  | use caps c p log =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hchk
      refine ⟨cleanProg_tail hclean, hchk.2, hcaps, ?_⟩
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hcaps hchk.1
      · exact hlog d hd
  | grant caps c p log =>
      exact absurd (List.mem_cons_self ..) (hclean c)

theorem inv_reach {policy : Finset Cap} {s t : State} (h : Reach s t)
    (hs : Inv policy s) : Inv policy t := by
  induction h with
  | refl => exact hs
  | tail _ hstep ih => exact inv_step hstep ih

/-- **Soundness of the isolation engine.**  A clean, certified app never
performs an effect outside its policy. -/
theorem no_escape_of_clean_of_proved {a : App} (hc : Clean a) (hp : Proved a) :
    ¬ Escapes a := by
  rintro ⟨s, hreach, c, hcmem, hcnot⟩
  have hinit : Inv a.policy (init a) := by
    refine ⟨hc, hp, subset_rfl, ?_⟩
    intro d hd
    simp [init] at hd
  exact hcnot ((inv_reach hreach hinit).2.2.2 c hcmem)

/-- **Main theorem.**  No app is simultaneously clean, proved, and escaping. -/
theorem no_clean_proved_with_escape :
    ¬ ∃ a : App, Clean a ∧ Proved a ∧ Escapes a := by
  rintro ⟨a, hc, hp, he⟩
  exact no_escape_of_clean_of_proved hc hp he

/-! ## Completeness

For clean apps the checker is not merely sound but exact: a clean app that
fails its certificate really does have a reachable escape.
-/

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

theorem exists_bad_use_of_check_false {caps : Finset Cap} {p : List Instr}
    (hclean : CleanProg p) (h : check caps p = false) :
    ∃ c : Cap, Instr.use c ∈ p ∧ c ∉ caps := by
  induction p with
  | nil => simp [check] at h
  | cons i rest ih =>
      cases i with
      | use d =>
          simp only [check, Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
          rcases h with h | h
          · exact ⟨d, List.mem_cons_self .., h⟩
          · obtain ⟨c, hc, hcn⟩ := ih (cleanProg_tail hclean) h
            exact ⟨c, List.mem_cons_of_mem _ hc, hcn⟩
      | grant d => exact absurd (List.mem_cons_self ..) (hclean d)

/-- **Completeness of the isolation engine (for clean apps).**  A clean app is
certified exactly when it cannot escape. -/
theorem proved_iff_not_escapes_of_clean {a : App} (hc : Clean a) :
    Proved a ↔ ¬ Escapes a := by
  refine ⟨fun hp => no_escape_of_clean_of_proved hc hp, fun hne => ?_⟩
  by_contra hp
  have hfalse : check a.policy a.prog = false := by
    simpa [Proved, Bool.not_eq_true] using hp
  obtain ⟨c, hcmem, hcnot⟩ := exists_bad_use_of_check_false hc hfalse
  obtain ⟨s, hs, hcs⟩ :=
    exists_reach_log_of_mem_use (caps := a.policy) (log := ([] : List Cap)) hcmem
  exact hne ⟨s, hs, c, hcs, hcnot⟩

/-! ## Non-vacuity: both hypotheses are load-bearing -/

/-- A *proved but unclean* app that does escape: the escape hatch really is
necessary in the main theorem. -/
theorem exists_proved_escaping_unclean :
    ∃ a : App, Proved a ∧ Escapes a ∧ ¬ Clean a := by
  refine ⟨⟨(∅ : Finset Cap), [Instr.grant 0, Instr.use 0]⟩, by simp [Proved, check], ?_, ?_⟩
  · refine ⟨⟨{0}, [], [0]⟩, ?_, 0, by simp, by simp⟩
    refine Relation.ReflTransGen.head (Step.grant ∅ 0 [Instr.use 0] []) ?_
    simpa using Relation.ReflTransGen.single
      (Step.use (insert 0 (∅ : Finset Cap)) 0 [] [])
  · intro h
    exact h 0 (by simp)

/-- A *clean but unproved* app that does escape: the certificate really is
necessary in the main theorem. -/
theorem exists_clean_escaping_unproved :
    ∃ a : App, Clean a ∧ Escapes a ∧ ¬ Proved a := by
  refine ⟨⟨(∅ : Finset Cap), [Instr.use 0]⟩, ?_, ?_, by simp [Proved, check]⟩
  · intro c hc
    simp at hc
  · exact ⟨⟨∅, [], [0]⟩, Relation.ReflTransGen.single (Step.use ∅ 0 [] []),
      0, by simp, by simp⟩

end PCA.Isolation

