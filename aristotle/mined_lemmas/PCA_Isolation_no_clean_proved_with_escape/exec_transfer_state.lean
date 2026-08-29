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

theorem exec_transfer_state {p : Prog} {A c : CapSet} {t : List Region}
    (hx : Exec p A c t) :
    ∀ (r : Region) (B : CapSet), c r = true → (A r = true → B r = true) →
      ∃ b t', Exec p B b t' ∧ b r = true := by
  induction hx with
  | nop h => intro r B hc hAB; exact ⟨B, [], .nop B, hAB hc⟩
  | acquire s h =>
      intro r B hc hAB
      refine ⟨insertCap s B, [], .acquire s B, ?_⟩
      rcases mem_insertCap.mp hc with hc | hc
      · exact mem_insertCap.mpr (Or.inl hc)
      · exact mem_insertCap.mpr (Or.inr (hAB hc))
  | release s h =>
      intro r B hc hAB
      refine ⟨eraseCap s B, [], .release s B, ?_⟩
      rcases mem_eraseCap.mp hc with ⟨h1, h2⟩
      exact mem_eraseCap.mpr ⟨h1, hAB h2⟩
  | accessOk s h hs =>
      intro r B hc hAB
      obtain ⟨b, t', e⟩ := exec_progress (.access s) B
      refine ⟨b, t', e, ?_⟩
      cases e <;> exact hAB hc
  | accessDenied s h hs =>
      intro r B hc hAB
      obtain ⟨b, t', e⟩ := exec_progress (.access s) B
      refine ⟨b, t', e, ?_⟩
      cases e <;> exact hAB hc
  | seq e₁ e₂ ih₁ ih₂ =>
      rename_i p q h h₁ h₂ t₁ t₂
      intro r B hc hAB
      by_cases hm : h₁ r = true
      · obtain ⟨b₁, t₁', ex₁, hb₁⟩ := ih₁ r B hm hAB
        obtain ⟨b, t₂', ex₂, hb⟩ := ih₂ r b₁ hc (fun _ => hb₁)
        exact ⟨b, t₁' ++ t₂', .seq ex₁ ex₂, hb⟩
      · obtain ⟨b₁, t₁', ex₁⟩ := exec_progress p B
        obtain ⟨b, t₂', ex₂, hb⟩ := ih₂ r b₁ hc (fun hh => absurd hh hm)
        exact ⟨b, t₁' ++ t₂', .seq ex₁ ex₂, hb⟩
  | choiceL e ih =>
      intro r B hc hAB
      obtain ⟨b, t', ex, hb⟩ := ih r B hc hAB
      exact ⟨b, t', .choiceL ex, hb⟩
  | choiceR e ih =>
      intro r B hc hAB
      obtain ⟨b, t', ex, hb⟩ := ih r B hc hAB
      exact ⟨b, t', .choiceR ex, hb⟩

/-- Transfer of an *observed access* to a smaller initial capability set. -/
