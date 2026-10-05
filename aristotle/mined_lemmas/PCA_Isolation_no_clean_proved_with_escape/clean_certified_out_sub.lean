import PCA.Isolation

/-!
# No Clean Proved With Escape
Category: Proof-Carrying Apps
Target: PCA.Isolation.no_clean_proved_with_escape
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Isolation

/-- Resources that a proof-carrying app may touch (files, sockets, ...). -/
abbrev Resource := Nat

/-- A capability set: the resources an app is entitled to touch. -/
abbrev Caps := Resource → Prop

/-- Inclusion of capability sets. -/

theorem clean_certified_out_sub {S T : Caps} {p : Prog}
    (hc : Certified S p T) (hcl : Clean p) : Caps.Sub T S := by
  induction hc with
  | nop => exact fun _ h => h
  | access _ => exact fun _ h => h
  | grant => exact hcl.elim
  | seq _ _ ih₁ ih₂ => exact fun r h => ih₁ hcl.1 r (ih₂ hcl.2 r h)
  | choice _ _ ih₁ _ => exact ih₁ hcl.1
  | loop _ _ => exact fun _ h => h
  | sub _ hSS' hTT' ih => exact fun r h => hSS' r (ih hcl r (hTT' r h))

/-- Auxiliary: soundness for a loop, given soundness for its body. -/
