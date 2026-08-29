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

theorem analyze_reachable : ∀ (p : Prog) (H : CapSet) (r : Region),
    analyze p H r = true → ∃ h' t, Exec p H h' t ∧ h' r = true := by
  intro p
  induction p with
  | nop => intro H r hr; exact ⟨H, [], .nop H, hr⟩
  | acquire s => intro H r hr; exact ⟨insertCap s H, [], .acquire s H, hr⟩
  | release s => intro H r hr; exact ⟨eraseCap s H, [], .release s H, hr⟩
  | access s =>
      intro H r hr
      obtain ⟨h', t, e⟩ := exec_progress (.access s) H
      refine ⟨h', t, e, ?_⟩
      cases e <;> exact hr
  | seq p q ihp ihq =>
      intro H r hr
      obtain ⟨m, tm, exm, hm⟩ := ihq (analyze p H) r hr
      by_cases hp : analyze p H r = true
      · obtain ⟨h₁, t₁, ex₁, h₁r⟩ := ihp H r hp
        obtain ⟨b, t₂, ex₂, hb⟩ := exec_transfer_state exm r h₁ hm (fun _ => h₁r)
        exact ⟨b, t₁ ++ t₂, .seq ex₁ ex₂, hb⟩
      · obtain ⟨h₁, t₁, ex₁⟩ := exec_progress p H
        obtain ⟨b, t₂, ex₂, hb⟩ := exec_transfer_state exm r h₁ hm (fun hh => absurd hh hp)
        exact ⟨b, t₁ ++ t₂, .seq ex₁ ex₂, hb⟩
  | choice p q ihp ihq =>
      intro H r hr
      rcases mem_unionCap.mp hr with hr | hr
      · obtain ⟨h', t, e, hh⟩ := ihp H r hr
        exact ⟨h', t, .choiceL e, hh⟩
      · obtain ⟨h', t, e, hh⟩ := ihq H r hr
        exact ⟨h', t, .choiceR e, hh⟩

/-- **Completeness of the checker.** If the engine rejects the app, then the app
really does have a run that escapes its policy. -/
