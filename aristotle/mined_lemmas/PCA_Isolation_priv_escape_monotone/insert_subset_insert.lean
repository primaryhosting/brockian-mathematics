/-!
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Isolation

/-- A set of privileges, represented by its membership predicate. -/

theorem insert_subset_insert {a : α} {S T : PrivSet α} (h : S ⊆ T) :
    insert a S ⊆ insert a T := by
  rintro b (rfl | hb)
  · exact Or.inl rfl
  · exact Or.inr (h hb)

end PrivSet

/-- A privilege-granting rule of the isolation engine: an app that already holds every
privilege in `guard` may additionally acquire the privilege `target`. -/
structure Rule (α : Type _) where
  /-- Privileges that must already be held for the rule to fire. -/
  guard : PrivSet α
  /-- Privilege granted when the rule fires. -/
  target : α

/-- A rule set (policy) of the isolation engine. -/
