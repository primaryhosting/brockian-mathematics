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

theorem eraseCap_mono {A B : CapSet} (h : CapSub A B) (r : Region) :
    CapSub (eraseCap r A) (eraseCap r B) := by
  intro x hx
  rcases mem_eraseCap.mp hx with ⟨h1, h2⟩
  exact mem_eraseCap.mpr ⟨h1, h x h2⟩

/-! ## Programs -/

/-- The application language of the isolation engine. -/
inductive Prog where
  /-- Do nothing. -/
  | nop : Prog
  /-- Ask the capability manager for a handle on region `r`. -/
  | acquire (r : Region) : Prog
  /-- Give back the handle on region `r`. -/
  | release (r : Region) : Prog
  /-- Try to touch region `r`. -/
  | access (r : Region) : Prog
  /-- Sequential composition. -/
  | seq (p q : Prog) : Prog
  /-- Nondeterministic choice (e.g. a data-dependent branch). -/
  | choice (p q : Prog) : Prog
  deriving DecidableEq, Repr

/-! ## Operational semantics of the isolation engine

`Exec p h h' t` : running `p` with capabilities `h` may terminate with
capabilities `h'`, observably touching exactly the regions listed in `t`.
The engine mediates every access: an access to a region whose capability is not
held is denied and leaves no observable effect. -/
inductive Exec : Prog → CapSet → CapSet → List Region → Prop where
  | nop (h : CapSet) : Exec .nop h h []
  | acquire (r : Region) (h : CapSet) : Exec (.acquire r) h (insertCap r h) []
  | release (r : Region) (h : CapSet) : Exec (.release r) h (eraseCap r h) []
  | accessOk (r : Region) (h : CapSet) (hr : h r = true) : Exec (.access r) h h [r]
  | accessDenied (r : Region) (h : CapSet) (hr : h r = false) : Exec (.access r) h h []
  | seq {p q : Prog} {h h₁ h₂ : CapSet} {t₁ t₂ : List Region} :
      Exec p h h₁ t₁ → Exec q h₁ h₂ t₂ → Exec (.seq p q) h h₂ (t₁ ++ t₂)
  | choiceL {p q : Prog} {h h' : CapSet} {t : List Region} :
      Exec p h h' t → Exec (.choice p q) h h' t
  | choiceR {p q : Prog} {h h' : CapSet} {t : List Region} :
      Exec q h h' t → Exec (.choice p q) h h' t

/-- The engine never gets stuck: every program has at least one run. -/
