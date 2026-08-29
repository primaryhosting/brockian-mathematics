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

theorem no_escape_cleanProved (a : App) (h : ¬ a.Escapes) : a.CleanProved := by
  have hclean : a.Clean := by
    unfold App.Clean
    cases hc : check a.policy a.code a.init with
    | true => rfl
    | false =>
        obtain ⟨h', t, e, esc⟩ := check_complete a.policy a.code a.init hc
        exact absurd ⟨h', t, e, esc⟩ h
  exact ⟨hclean, ⟨_, check_cert a.policy a.code a.init hclean⟩⟩

/-- **Target theorem.** No application can be simultaneously accepted by the
isolation engine's checker, carry a valid capability certificate, and still have
a run that escapes its sandbox policy. -/
