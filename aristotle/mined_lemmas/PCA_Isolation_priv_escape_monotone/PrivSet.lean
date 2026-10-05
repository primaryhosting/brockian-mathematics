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

def PrivSet (α : Type _) : Type _ := α → Prop

namespace PrivSet

variable {α : Type _}

instance : Membership α (PrivSet α) := ⟨fun S a => S a⟩

instance : HasSubset (PrivSet α) := ⟨fun S T => ∀ ⦃a⦄, a ∈ S → a ∈ T⟩

/-- Adding one privilege to a privilege set. -/
