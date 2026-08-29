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

theorem Policy.enc_injective : Function.Injective Policy.enc := by
  intro p q h
  obtain ⟨h1, h2⟩ := pairNat_inj h
  cases p; cases q
  simp only [Policy.mk.injEq]
  exact ⟨h1, encList_inj h2⟩

/-- The digest of an artifact.  It is collision-free (injective), so the model
captures the ideal-hash assumption used by proof-carrying deployments. -/
