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

def issue (a : Artifact) : Certificate := ⟨digest a⟩

/-- Re-proving (re-checking) a certificate against a presented artifact: the
engine recomputes the digest of what it is about to run and compares it with the
digest recorded in the certificate. -/
