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

theorem exists_tampered_detected :
    ∃ (orig : Artifact) (b : Bundle),
      CertPreserving stdEngine orig b ∧ ¬ Untampered stdEngine orig b ∧
        stdEngine.reprove b ≠ b.cert := by
  refine ⟨⟨[0], [], []⟩, ⟨⟨[1], [], []⟩, (stdEngine.sealArtifact ⟨[0], [], []⟩).cert⟩,
    (rfl : ((⟨⟨[1], [], []⟩, (stdEngine.sealArtifact ⟨[0], [], []⟩).cert⟩ : Bundle)).cert
      = (stdEngine.sealArtifact ⟨[0], [], []⟩).cert), ?_, ?_⟩
  · intro h
    have : ([1] : Bytes) = [0] := congrArg (fun x => x.artifact.code) h
    simp at this
  · intro h
    have hd : stdDigest ⟨[1], [], []⟩ = stdDigest ⟨[0], [], []⟩ :=
      congrArg Certificate.bound h
    have h0 : (Artifact.mk [1] [] []) = Artifact.mk [0] [] [] := stdDigest_injective hd
    simp [Artifact.mk.injEq] at h0

end Cert
end PCA

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

