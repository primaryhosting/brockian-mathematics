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

theorem clean_certified_run_sub {S T : Caps} {p : Prog}
    (hc : Certified S p T) (hcl : Clean p) :
    ∀ t, Run p t → ∀ r ∈ t, S r := by
  induction hc with
  | nop =>
      intro t ht
      cases ht
      exact fun r hr => absurd hr List.not_mem_nil
  | @access S r hr =>
      intro t ht
      cases ht
      intro s hs
      cases List.mem_singleton.1 hs
      exact hr
  | grant => exact hcl.elim
  | @seq S T U p q hp _ ih₁ ih₂ =>
      intro t ht
      cases ht with
      | seq h₁ h₂ =>
          intro r hr
          rcases List.mem_append.1 hr with h | h
          · exact ih₁ hcl.1 _ h₁ r h
          · exact clean_certified_out_sub hp hcl.1 r (ih₂ hcl.2 _ h₂ r h)
  | choice _ _ ih₁ ih₂ =>
      intro t ht
      cases ht with
      | choiceL h => exact ih₁ hcl.1 _ h
      | choiceR h => exact ih₂ hcl.2 _ h
  | loop _ ih => exact run_loop_sub (ih hcl)
  | sub _ hSS' _ ih =>
      intro t ht r hr
      exact hSS' r (ih hcl t ht r hr)

/-- **Main result.**  There is no clean app that the isolation engine certifies
against a policy and that nevertheless escapes that policy at run time. -/
