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

theorem encodeField_append_inj {l₁ l₂ x y : List Nat}
    (h : encodeField l₁ ++ x = encodeField l₂ ++ y) : l₁ = l₂ ∧ x = y := by
  simp only [encodeField, List.cons_append, List.cons.injEq] at h
  exact List.append_inj h.2 h.1

/-- The digest is injective: distinct artifacts have distinct digests. -/
