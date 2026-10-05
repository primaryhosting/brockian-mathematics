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

theorem cert_sound {P H K : CapSet} {p : Prog} (c : Cert P H p K) :
    ∀ {h h' : CapSet} {t : List Region}, CapSub h H → Exec p h h' t →
      (∀ r, r ∈ t → P r = true) ∧ CapSub h' K := by
  induction c with
  | nop H =>
      intro h h' t hsub e
      cases e
      exact ⟨by simp, hsub⟩
  | acquire H r =>
      intro h h' t hsub e
      cases e
      exact ⟨by simp, insertCap_mono hsub r⟩
  | release H r =>
      intro h h' t hsub e
      cases e
      exact ⟨by simp, eraseCap_mono hsub r⟩
  | access H r hr =>
      intro h h' t hsub e
      cases e with
      | accessOk _ _ hmem =>
          refine ⟨?_, hsub⟩
          intro s hs
          simp only [List.mem_singleton] at hs
          subst hs
          exact hr (hsub s hmem)
      | accessDenied _ _ _ => exact ⟨by simp, hsub⟩
  | seq c₁ c₂ ih₁ ih₂ =>
      intro h h' t hsub e
      cases e with
      | seq e₁ e₂ =>
          obtain ⟨ht₁, hs₁⟩ := ih₁ hsub e₁
          obtain ⟨ht₂, hs₂⟩ := ih₂ hs₁ e₂
          refine ⟨?_, hs₂⟩
          intro s hs
          rcases List.mem_append.mp hs with hs | hs
          · exact ht₁ s hs
          · exact ht₂ s hs
  | choice c₁ c₂ ih₁ ih₂ =>
      intro h h' t hsub e
      cases e with
      | choiceL e =>
          obtain ⟨ht, hs⟩ := ih₁ hsub e
          exact ⟨ht, fun x hx => mem_unionCap.mpr (Or.inl (hs x hx))⟩
      | choiceR e =>
          obtain ⟨ht, hs⟩ := ih₂ hsub e
          exact ⟨ht, fun x hx => mem_unionCap.mpr (Or.inr (hs x hx))⟩
  | conseq hHH c hKK ih =>
      intro h h' t hsub e
      obtain ⟨ht, hs⟩ := ih (fun x hx => hHH x (hsub x hx)) e
      exact ⟨ht, fun x hx => hKK x (hs x hx)⟩

/-! ## The engine's checker

`analyze p H` computes the capabilities that may be held after running `p` from
capabilities `H` (exactly: see `analyze_reachable`); `check P p H` is the
decidable acceptance test. -/
