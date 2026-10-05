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

theorem exists_clean_certified_run :
    ∃ (p : Prog) (P T : Caps) (t : List Resource),
      Clean p ∧ Certified P p T ∧ Run p t ∧ t ≠ [] := by
  refine ⟨.loop (.access 0), fun r => r = 0, fun r => r = 0, [0], trivial,
    Certified.loop (Certified.access rfl), ?_, by simp⟩
  have h := Run.loopStep (Run.access 0) (Run.loopDone (p := .access 0))
  simpa using h

/-- Sharpness: the cleanliness hypothesis cannot be dropped — an app using the
`grant` escape hatch can be certified and still escape its policy. -/
