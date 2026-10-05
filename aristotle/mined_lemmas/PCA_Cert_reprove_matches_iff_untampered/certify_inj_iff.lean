/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Cert

/-- An *artifact* shipped by a proof-carrying app: a code segment together with a data
segment, both modelled as lists of machine words. -/
structure Artifact where
  code : List Nat
  data : List Nat
  deriving DecidableEq, Repr

/-- A *certificate* accompanying an artifact: the digest computed by the isolation engine's
prover at seal time. -/
structure Certificate where
  digest : List Nat
  deriving DecidableEq, Repr

/-- The (collision-free) digest of an artifact: the length of the code segment, followed by
the concatenation of the code and data segments.  The length prefix makes the encoding
uniquely decodable, so the digest determines the artifact. -/

theorem certify_inj_iff {a b : Artifact} : certify a = certify b ↔ a = b :=
  ⟨fun h => certify_injective h, fun h => h ▸ rfl⟩

/-- **Soundness and completeness of the isolation engine's integrity check.**

Given the certificate produced for the original artifact, the verifier's `reprove` step
succeeds on a received artifact if and only if that artifact is untampered:

* (⇐, completeness) an untampered artifact always reproves successfully;
* (⇒, soundness) any artifact that reproves successfully is bit-for-bit the original. -/
