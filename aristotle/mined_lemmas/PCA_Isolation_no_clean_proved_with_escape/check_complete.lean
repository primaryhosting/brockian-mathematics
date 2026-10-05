/-!
# No Clean Proved With Escape
Category: Proof-Carrying Apps
Target: PCA.Isolation.no_clean_proved_with_escape
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This module formalises the model of a capability-based *isolation engine* for
proof-carrying applications, together with its soundness **and** completeness.

* A region (`Region`) is an abstract resource name; a capability set (`CapSet`)
  is a decidable set of regions, represented by its characteristic function.
* An application's code is a program (`Prog`) of a small nondeterministic
  language with capability acquisition/release and resource accesses.
* `Exec` is the operational semantics of the isolation engine at run time: a
  resource access only produces an observable effect when the corresponding
  capability is currently held; otherwise the engine *denies* it silently.
* `App.Escapes` says that some run of the application observably touches a
  resource outside its policy (its sandbox boundary).
* `Cert` is the proof system for capability certificates that a proof-carrying
  app ships with its code, and `check` is the engine's decidable checker.

The main results are:

* `cert_sound`  : a valid certificate forbids any escape;
* `check_cert`  : the checker synthesises a certificate (so `Clean → Proved`);
* `check_complete` : if the checker rejects, an escaping run really exists;
* `no_clean_proved_with_escape` : the target theorem;
* `clean_proved_iff_no_escape` : soundness *and* completeness of the engine.

The development is deliberately self-contained (no imports), so that the header
comment above is literally the first thing in the file.
-/

namespace PCA.Isolation

/-! ## Capability sets -/

/-- Abstract resource names. -/
abbrev Region := Nat

/-- A capability set, represented by its characteristic function. -/
abbrev CapSet := Region → Bool

/-- Add a capability. -/

theorem check_complete (P : CapSet) : ∀ (p : Prog) (H : CapSet),
    check P p H = false → ∃ h' t, Exec p H h' t ∧ EscapingTrace P t := by
  intro p
  induction p with
  | nop => intro H hc; simp [check] at hc
  | acquire r => intro H hc; simp [check] at hc
  | release r => intro H hc; simp [check] at hc
  | access r =>
      intro H hc
      simp only [check, Bool.or_eq_false_iff, Bool.not_eq_false'] at hc
      exact ⟨H, [r], .accessOk r H hc.1, ⟨r, by simp, hc.2⟩⟩
  | seq p q ihp ihq =>
      intro H hc
      simp only [check, Bool.and_eq_false_iff] at hc
      rcases hc with hc | hc
      · obtain ⟨h₁, t₁, ex₁, r, hr, hP⟩ := ihp H hc
        obtain ⟨h₂, t₂, ex₂⟩ := exec_progress q h₁
        exact ⟨h₂, t₁ ++ t₂, .seq ex₁ ex₂, ⟨r, by simp [hr], hP⟩⟩
      · obtain ⟨m, tm, exm, r, hr, hP⟩ := ihq (analyze p H) hc
        by_cases hpr : analyze p H r = true
        · obtain ⟨h₁, t₁, ex₁, h₁r⟩ := analyze_reachable p H r hpr
          obtain ⟨b, t₂, ex₂, hb⟩ := exec_transfer_trace exm r h₁ hr (fun _ => h₁r)
          exact ⟨b, t₁ ++ t₂, .seq ex₁ ex₂, ⟨r, by simp [hb], hP⟩⟩
        · obtain ⟨h₁, t₁, ex₁⟩ := exec_progress p H
          obtain ⟨b, t₂, ex₂, hb⟩ := exec_transfer_trace exm r h₁ hr (fun hh => absurd hh hpr)
          exact ⟨b, t₁ ++ t₂, .seq ex₁ ex₂, ⟨r, by simp [hb], hP⟩⟩
  | choice p q ihp ihq =>
      intro H hc
      simp only [check, Bool.and_eq_false_iff] at hc
      rcases hc with hc | hc
      · obtain ⟨h', t, e, esc⟩ := ihp H hc
        exact ⟨h', t, .choiceL e, esc⟩
      · obtain ⟨h', t, e, esc⟩ := ihq H hc
        exact ⟨h', t, .choiceR e, esc⟩

/-! ## Applications and the isolation guarantee -/

/-- A proof-carrying application: its sandbox policy, the capabilities it starts
with, and its code. -/
structure App where
  /-- The sandbox boundary: the regions the app is allowed to touch. -/
  policy : CapSet
  /-- The capabilities the app starts with. -/
  init : CapSet
  /-- The app's code. -/
  code : Prog

/-- The app has a run that observably touches a region outside its policy. -/
