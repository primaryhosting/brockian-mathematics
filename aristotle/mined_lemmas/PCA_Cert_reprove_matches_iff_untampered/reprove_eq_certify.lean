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

theorem reprove_eq_certify (a : Artifact) :
    reprove hash claimOf a = certify hash claimOf a := rfl

/-- **Soundness and completeness of the isolation engine's tamper check.**

Given a collision-free digest function `hash`, a certificate `c` issued for the
original artifact `orig`, and a received artifact `recv`, re-proving `recv`
reproduces the certificate `c` exactly when `recv` has not been tampered with,
i.e. when `recv = orig`.

Left-to-right is soundness of the check: a matching re-proof witnesses integrity.
Right-to-left is completeness: an untampered artifact always re-certifies to the
same certificate, since the checker is deterministic. -/
