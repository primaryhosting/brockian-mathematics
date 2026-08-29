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

def EscapingTrace (P : CapSet) (t : List Region) : Prop := ∃ r, r ∈ t ∧ P r = false

/-! ## Certificates

A certificate is a derivation of `Cert P H p K`, read as: if the app starts with
capabilities contained in `H`, then running `p` touches only regions allowed by
the policy `P`, and ends with capabilities contained in `K`. -/
inductive Cert (P : CapSet) : CapSet → Prog → CapSet → Prop where
  | nop (H : CapSet) : Cert P H .nop H
  | acquire (H : CapSet) (r : Region) : Cert P H (.acquire r) (insertCap r H)
  | release (H : CapSet) (r : Region) : Cert P H (.release r) (eraseCap r H)
  | access (H : CapSet) (r : Region) (h : H r = true → P r = true) :
      Cert P H (.access r) H
  | seq {H K L : CapSet} {p q : Prog} :
      Cert P H p K → Cert P K q L → Cert P H (.seq p q) L
  | choice {H K₁ K₂ : CapSet} {p q : Prog} :
      Cert P H p K₁ → Cert P H q K₂ → Cert P H (.choice p q) (unionCap K₁ K₂)
  | conseq {H H' K K' : CapSet} {p : Prog} :
      CapSub H' H → Cert P H p K → CapSub K K' → Cert P H' p K'

/-- **Soundness of certificates.** A certified program, started with capabilities
inside its precondition, only touches regions allowed by the policy, and ends
inside its postcondition. -/
