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

theorem run_loop_sub {p : Prog} {S : Caps}
    (hbody : ∀ t, Run p t → ∀ r ∈ t, S r) :
    ∀ t, Run (.loop p) t → ∀ r ∈ t, S r := by
  intro t ht
  generalize hq : Prog.loop p = q at ht
  induction ht with
  | nop => cases hq
  | access r => cases hq
  | grant r => cases hq
  | seq _ _ _ _ => cases hq
  | choiceL _ _ => cases hq
  | choiceR _ _ => cases hq
  | loopDone => exact fun r hr => absurd hr List.not_mem_nil
  | loopStep hb _ _ ih₂ =>
      cases hq
      intro r hr
      rcases List.mem_append.1 hr with h | h
      · exact hbody _ hb r h
      · exact ih₂ rfl r h

/-- **Soundness of the isolation engine on clean apps.**
Every access performed by a certified clean app lies inside the capability set
the certificate started from. -/
