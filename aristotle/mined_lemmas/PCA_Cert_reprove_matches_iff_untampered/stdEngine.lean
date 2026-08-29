/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the header above is a module docstring, and Lean requires every `import` to come
-- before any command, so this module carries no imports and is developed in core Lean 4.
-- It compiles unchanged inside this Mathlib project.

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA
namespace Cert

/-! ## The isolation engine's model

A *proof-carrying app* is shipped as a **bundle**: the artifact that will actually be
executed inside the isolation sandbox, together with a **certificate** that the isolation
engine issued when it admitted (sealed) that artifact.

At load time the engine's only capability is to *re-prove*: it recomputes, from the
artifact actually in front of it, the digest that the accompanying certificate ought to
carry.  The security claim of the architecture is that this cheap recomputation is an
*exact* tamper detector.  That is `reprove_matches_iff_untampered` below: soundness (a
matching re-proof implies the bundle really is the sealed one) and completeness (the
sealed bundle always re-proves, so honest deployments are never rejected) at once.
-/

/-- Raw serialized data. -/
abbrev Bytes : Type := List Nat

/-- Digests produced by the engine's measurement function. -/
abbrev Digest : Type := List Nat

/-- An artifact submitted to the isolation engine: the executable image, the
specification it is claimed to meet, and the sandbox policy it must run under. -/
structure Artifact where
  /-- The executable image. -/
  code : Bytes
  /-- The specification the image is claimed to satisfy. -/
  spec : Bytes
  /-- The isolation policy the image must be run under. -/
  policy : Bytes
deriving DecidableEq

/-- A certificate: the digest the engine bound to the artifact at sealing time. -/
structure Certificate where
  /-- The digest bound by the engine. -/
  bound : Digest
deriving DecidableEq

/-- A deployed bundle: an artifact together with the certificate travelling with it. -/
structure Bundle where
  /-- The artifact that would be executed. -/
  artifact : Artifact
  /-- The certificate accompanying the artifact. -/
  cert : Certificate
deriving DecidableEq

/-- An isolation engine is a measurement function on artifacts that is collision free:
distinct artifacts receive distinct digests. -/
structure Engine where
  /-- The measurement (digest) function. -/
  digest : Artifact → Digest
  /-- Collision freedom of the measurement function. -/
  collision_free : Function.Injective digest

namespace Engine

variable (E : Engine)

/-- Sealing: the engine admits an artifact and issues the bundle that gets deployed. -/

def stdEngine : Engine := ⟨stdDigest, stdDigest_injective⟩

/-- The main theorem, instantiated at the concrete engine. -/
