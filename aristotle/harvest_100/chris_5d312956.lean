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
def caps : Prog Cap → Cap → Prop
  | .nop, _ => False
  | .use c, d => d = c
  | .seq p q, d => caps p d ∨ caps q d
  | .branch p q, d => caps p d ∨ caps q d
  | .loop p, d => caps p d

/-- An isolation policy: the predicate describing which capabilities the sandbox permits. -/
structure Policy (Cap : Type u) : Type u where
  /-- The permitted capabilities. -/
  allowed : Cap → Prop

/-- The certificate check performed by the isolation engine: the app is *proved clean*
against a policy when every statically predicted capability is permitted by the policy. -/
def Proved (pol : Policy Cap) (p : Prog Cap) : Prop :=
  ∀ c, caps p c → pol.allowed c

/-- The app *escapes* the sandbox when some possible run-time trace exercises a
capability the policy does not permit. -/
def Escapes (pol : Policy Cap) (p : Prog Cap) : Prop :=
  ∃ t, Runs p t ∧ ∃ c, c ∈ t ∧ ¬ pol.allowed c

/-- Soundness of the static analysis: every capability appearing in a run-time trace of
`p` is predicted by `caps p`. -/
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
theorem no_clean_proved_with_escape (pol : Policy Cap) (p : Prog Cap) :
    ¬ (Proved pol p ∧ Escapes pol p) := by
  rintro ⟨hproved, t, hruns, c, hct, hc⟩
  exact hc (hproved c (caps_of_mem_trace hruns c hct))

/-- Positive form of the main theorem: every run-time trace of a proved-clean app only
exercises capabilities the policy permits. -/
theorem allowed_of_mem_trace_of_proved {pol : Policy Cap} {p : Prog Cap}
    (hproved : Proved pol p) {t : List Cap} (hruns : Runs p t) :
    ∀ c ∈ t, pol.allowed c :=
  fun c hc => hproved c (caps_of_mem_trace hruns c hc)

/-- There is no policy and app at all exhibiting a proved-clean escape. -/
theorem not_exists_clean_proved_with_escape :
    ¬ ∃ (pol : Policy Cap) (p : Prog Cap), Proved pol p ∧ Escapes pol p := by
  rintro ⟨pol, p, h⟩
  exact no_clean_proved_with_escape pol p h

/-- Exactness of the engine's verdict: an app escapes its sandbox precisely when the
certificate check fails. -/
theorem escapes_iff_not_proved (pol : Policy Cap) (p : Prog Cap) :
    Escapes pol p ↔ ¬ Proved pol p := by
  constructor
  · intro h hproved
    exact no_clean_proved_with_escape pol p ⟨hproved, h⟩
  · intro h
    refine Classical.byContradiction fun hesc => h ?_
    intro c hc
    refine Classical.byContradiction fun hnall => hesc ?_
    obtain ⟨t, ht, hct⟩ := exists_trace_mem_of_caps hc
    exact ⟨t, ht, c, hct, hnall⟩

/-- Non-vacuity: escapes really can happen for apps that fail the certificate check.
With capabilities `Bool` and a policy permitting only `true`, the app `use false`
escapes (and, by the theorem above, is therefore not proved clean). -/
example : Escapes (Policy.mk (fun c : Bool => c = true)) (Prog.use false) :=
  ⟨[false], Runs.use false, false, by simp, by simp⟩

end PCA.Isolation

