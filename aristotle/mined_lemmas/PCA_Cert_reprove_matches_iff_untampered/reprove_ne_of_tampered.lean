/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header comment above is a module docstring, which Lean treats
-- as a command; consequently no `import` line may follow it.  The development below
-- is therefore self-contained and uses only the Lean 4 core library.

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

/-- An artifact shipped by the isolation engine: a code image together with the
policy/configuration it is meant to run under. -/
structure Artifact where
  /-- The code image, as a byte (word) list. -/
  code : List Nat
  /-- The policy/configuration image, as a byte (word) list. -/
  policy : List Nat
deriving DecidableEq

/-- A length-prefixed serialization of an artifact.  The length prefix makes the
encoding unambiguous, i.e. injective. -/

theorem reprove_ne_of_tampered
    (hinj : Function.Injective hash)
    (orig recv : Artifact) (c : Cert) (hc : c = certify hash claimOf orig)
    (htamper : recv ≠ orig) :
    reprove hash claimOf recv ≠ c := by
  intro h
  exact htamper ((reprove_matches_iff_untampered hash claimOf hinj orig recv c hc).mp h)

end Cert

end PCA

#print axioms PCA.Cert.reprove_matches_iff_untampered

