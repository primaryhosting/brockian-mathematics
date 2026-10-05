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

theorem exec_progress (p : Prog) (h : CapSet) : ∃ h' t, Exec p h h' t := by
  induction p generalizing h with
  | nop => exact ⟨h, [], .nop h⟩
  | acquire r => exact ⟨insertCap r h, [], .acquire r h⟩
  | release r => exact ⟨eraseCap r h, [], .release r h⟩
  | access r =>
      cases hr : h r with
      | false => exact ⟨h, [], .accessDenied r h hr⟩
      | true => exact ⟨h, [r], .accessOk r h hr⟩
  | seq p q ihp ihq =>
      obtain ⟨h₁, t₁, e₁⟩ := ihp h
      obtain ⟨h₂, t₂, e₂⟩ := ihq h₁
      exact ⟨h₂, t₁ ++ t₂, .seq e₁ e₂⟩
  | choice p q ihp _ =>
      obtain ⟨h', t, e⟩ := ihp h
      exact ⟨h', t, .choiceL e⟩

/-! ## Escapes -/

/-- A trace escapes the policy `P` if it observably touches a region outside `P`. -/
