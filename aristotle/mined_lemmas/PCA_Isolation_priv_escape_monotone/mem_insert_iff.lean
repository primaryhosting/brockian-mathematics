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

@[simp] theorem mem_insert_iff {a b : α} {S : PrivSet α} :
    b ∈ insert a S ↔ b = a ∨ b ∈ S := Iff.rfl

