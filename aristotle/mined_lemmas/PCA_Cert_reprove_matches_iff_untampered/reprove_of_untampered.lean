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

theorem reprove_of_untampered (a a' : Artifact) (h : a' = a) : reprove a' = reprove a :=
  (reprove_matches_iff_untampered a a').2 h

/-- Soundness / tamper detection: any modification of the artifact is detected. -/
