/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA
namespace Cert

/-- An application artifact as seen by the isolation engine: the executable code,
the configuration it is launched with, and the isolation policy it is bound to.
Each component is modelled as a byte string (a list of naturals). -/
structure Artifact where
  code : List Nat
  config : List Nat
  policy : List Nat
  deriving DecidableEq

/-- Length-prefixed encoding of a single byte string. -/

theorem digest_injective : Function.Injective digest := by
  rintro ⟨c₁, g₁, p₁⟩ ⟨c₂, g₂, p₂⟩ h
  simp only [digest] at h
  obtain ⟨hc, h⟩ := encodeField_append_inj h
  obtain ⟨hg, hp⟩ := encodeField_append_inj h
  have hp' : p₁ = p₂ := (encodeField_append_inj (x := ([] : List Nat)) (y := [])
    (by simpa using hp)).1
  subst hc; subst hg; subst hp'
  rfl

/-- **Soundness and completeness of certificate re-proving.**
Re-checking the certificate issued for `orig` against a presented artifact `a`
succeeds if and only if `a` is untampered, i.e. `a = orig`.

Soundness: a successful re-check implies the artifact is bit-for-bit the one the
proof was produced for. Completeness: an untampered artifact always re-checks. -/
