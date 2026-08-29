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

theorem Subset.trans {S T U : PrivSet α} (h₁ : S ⊆ T) (h₂ : T ⊆ U) : S ⊆ U :=
  fun _ h => h₂ (h₁ h)

