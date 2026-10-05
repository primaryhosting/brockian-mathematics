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

theorem check_cert (P : CapSet) : ∀ (p : Prog) (H : CapSet),
    check P p H = true → Cert P H p (analyze p H) := by
  intro p
  induction p with
  | nop => intro H _; exact .nop H
  | acquire r => intro H _; exact .acquire H r
  | release r => intro H _; exact .release H r
  | access r =>
      intro H hc
      refine .access H r ?_
      intro hH
      simp [check, hH] at hc
      exact hc
  | seq p q ihp ihq =>
      intro H hc
      simp only [check, Bool.and_eq_true] at hc
      exact .seq (ihp H hc.1) (ihq (analyze p H) hc.2)
  | choice p q ihp ihq =>
      intro H hc
      simp only [check, Bool.and_eq_true] at hc
      exact .choice (ihp H hc.1) (ihq H hc.2)

/-! ## Exactness of the analysis

The two transfer lemmas below say that the analysis is not merely a sound
over-approximation: anything it predicts is genuinely realisable by a run. -/

/-- Transfer of a *held capability* to a smaller initial capability set. -/
