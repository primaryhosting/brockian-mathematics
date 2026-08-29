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
def sealArtifact (a : Artifact) : Bundle := ⟨a, ⟨E.digest a⟩⟩

/-- Re-proving: the engine recomputes, from the artifact actually present in the bundle,
the certificate that this bundle ought to be carrying. -/
def reprove (b : Bundle) : Certificate := ⟨E.digest b.artifact⟩

@[simp] theorem sealArtifact_artifact (a : Artifact) : (E.sealArtifact a).artifact = a := rfl

@[simp] theorem sealArtifact_cert (a : Artifact) : (E.sealArtifact a).cert = ⟨E.digest a⟩ := rfl

@[simp] theorem reprove_sealArtifact (a : Artifact) : E.reprove (E.sealArtifact a) = (E.sealArtifact a).cert := rfl

end Engine

/-- A bundle is *untampered* with respect to an original artifact when it is exactly the
bundle the engine sealed for that artifact. -/
def Untampered (E : Engine) (orig : Artifact) (b : Bundle) : Prop :=
  b = E.sealArtifact orig

/-- The adversary model: the attacker may swap the artifact for anything at all, but the
bundle still presents the certificate that the engine issued for `orig` — a certificate
issued for some other artifact is not a certificate *for this deployment*. -/
def CertPreserving (E : Engine) (orig : Artifact) (b : Bundle) : Prop :=
  b.cert = (E.sealArtifact orig).cert

theorem certPreserving_sealArtifact (E : Engine) (orig : Artifact) :
    CertPreserving E orig (E.sealArtifact orig) := rfl

/-! ## Main theorem -/

/-- **Re-proving matches iff the bundle is untampered.**

For any deployment carrying the certificate the engine issued for `orig`, the engine's
recomputed certificate agrees with the carried certificate *exactly* when the bundle is
the untampered sealed bundle.

* (→) *Soundness of tamper detection*: a successful re-proof cannot be forged — collision
  freedom of the measurement forces the shipped artifact to be `orig` itself, and then the
  preserved certificate forces the whole bundle to be `E.sealArtifact orig`.
* (←) *Completeness of tamper detection*: the genuine sealed bundle always re-proves, so
  the engine never rejects an honest deployment. -/
theorem reprove_matches_iff_untampered
    (E : Engine) (orig : Artifact) (b : Bundle) (hb : CertPreserving E orig b) :
    E.reprove b = b.cert ↔ Untampered E orig b := by
  have hb' : b.cert = (E.sealArtifact orig).cert := hb
  constructor
  · intro h
    have hd : E.digest b.artifact = E.digest orig := by
      have h' : (E.reprove b).bound = b.cert.bound := congrArg Certificate.bound h
      have hc : b.cert.bound = E.digest orig := congrArg Certificate.bound hb'
      simpa [Engine.reprove, hc] using h'
    have ha : b.artifact = orig := E.collision_free hd
    calc b = ⟨b.artifact, b.cert⟩ := rfl
      _ = ⟨orig, (E.sealArtifact orig).cert⟩ := by rw [ha, hb']
      _ = E.sealArtifact orig := rfl
  · intro h
    subst h
    exact E.reprove_sealArtifact orig

/-! ## Consequences -/

/-- Soundness: if the re-proof matches, nothing was tampered with. -/
theorem untampered_of_reprove_matches
    (E : Engine) (orig : Artifact) (b : Bundle) (hb : CertPreserving E orig b)
    (h : E.reprove b = b.cert) : Untampered E orig b :=
  (reprove_matches_iff_untampered E orig b hb).mp h

/-- Completeness: an honest sealed bundle always re-proves. -/
theorem reprove_matches_of_untampered
    (E : Engine) (orig : Artifact) (b : Bundle) (h : Untampered E orig b) :
    E.reprove b = b.cert := by
  subst h; exact E.reprove_sealArtifact orig

/-- Tamper detection: every cert-preserving modification of the sealed bundle is caught. -/
theorem reprove_ne_of_tampered
    (E : Engine) (orig : Artifact) (b : Bundle) (hb : CertPreserving E orig b)
    (h : ¬ Untampered E orig b) : E.reprove b ≠ b.cert :=
  fun hm => h ((reprove_matches_iff_untampered E orig b hb).mp hm)

/-! ## A concrete collision-free engine

The abstract hypothesis `Engine.collision_free` is satisfiable, so the theory above is not
vacuous: length-prefixing each field yields a self-delimiting (prefix-free) serialization,
whose concatenation is an injective measurement. -/

/-- Length-prefixed (self-delimiting) encoding of one field. -/
def encField (l : Bytes) : Bytes := l.length :: l

/-- Length prefixing is prefix free: an encoded field can be split off a concatenation in
only one way. -/
theorem encField_prefix_free {l₁ l₂ r₁ r₂ : Bytes}
    (h : encField l₁ ++ r₁ = encField l₂ ++ r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  have h' : l₁.length :: (l₁ ++ r₁) = l₂.length :: (l₂ ++ r₂) := by
    simpa [encField, List.cons_append] using h
  have hlen : l₁.length = l₂.length := (List.cons.inj h').1
  exact List.append_inj (List.cons.inj h').2 hlen

/-- The standard measurement: concatenate the length-prefixed fields. -/
def stdDigest (a : Artifact) : Digest :=
  encField a.code ++ encField a.spec ++ encField a.policy

theorem stdDigest_injective : Function.Injective stdDigest := by
  rintro ⟨c₁, s₁, p₁⟩ ⟨c₂, s₂, p₂⟩ h
  simp only [stdDigest, List.append_assoc] at h
  have h1 := encField_prefix_free (l₁ := c₁) (l₂ := c₂) h
  have h2 := encField_prefix_free (l₁ := s₁) (l₂ := s₂) h1.2
  have h3 : p₁ = p₂ := by
    have h4 : encField p₁ = encField p₂ := by simpa using h2.2
    exact ((List.cons.inj h4).2)
  simp [h1.1, h2.1, h3]

/-- The standard isolation engine. -/
def stdEngine : Engine := ⟨stdDigest, stdDigest_injective⟩

/-- The main theorem, instantiated at the concrete engine. -/
theorem std_reprove_matches_iff_untampered
    (orig : Artifact) (b : Bundle) (hb : CertPreserving stdEngine orig b) :
    stdEngine.reprove b = b.cert ↔ Untampered stdEngine orig b :=
  reprove_matches_iff_untampered stdEngine orig b hb

/-- Non-vacuity of the adversary model: cert-preserving tampered bundles do exist, and the
engine detects them. -/
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

