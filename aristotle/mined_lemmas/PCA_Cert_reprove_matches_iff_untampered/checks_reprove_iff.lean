/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Cert

/-! ## Arithmetic: an injective pairing function on `Nat` -/

/-- Szudzik-style pairing function. -/

theorem checks_reprove_iff (a a' : Artifact) :
    checks (reprove a) a' = true ↔ a' = a := by
  simp [checks, reprove_matches_iff_untampered]

/-! ## The certified verdict really does guarantee isolation -/

