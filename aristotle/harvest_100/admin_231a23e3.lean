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
def digestOf (a : Artifact) : List Nat :=
  a.code.length :: (a.code ++ a.data)

/-- The prover: produce the certificate of an artifact. -/
def certify (a : Artifact) : Certificate :=
  ⟨digestOf a⟩

/-- Sealing an artifact yields the artifact together with its certificate. -/
def sealBundle (a : Artifact) : Artifact × Certificate :=
  (a, certify a)

/-- The verifier's *reprove* step: recompute the digest of the received artifact and compare
it with the certificate that was received alongside it. -/
def reprove (recv : Artifact) (c : Certificate) : Bool :=
  decide (certify recv = c)

/-- A received artifact is *untampered* with respect to the original one exactly when it is
bit-for-bit the original one. -/
def Untampered (orig recv : Artifact) : Prop :=
  recv = orig

/-- The digest is collision-free: distinct artifacts have distinct digests.

The key library ingredient is `List.append_inj`, which cancels an append once the two left
factors are known to have equal lengths — and that length is exactly what the head field of
the digest records. -/
theorem digestOf_injective : Function.Injective digestOf := by
  rintro ⟨c₁, d₁⟩ ⟨c₂, d₂⟩ h
  simp only [digestOf, List.cons.injEq] at h
  obtain ⟨hlen, happ⟩ := h
  obtain ⟨hc, hd⟩ := List.append_inj happ hlen
  simp [hc, hd]

/-- Two artifacts have the same digest iff they are equal. -/
theorem digestOf_inj_iff {a b : Artifact} : digestOf a = digestOf b ↔ a = b :=
  ⟨fun h => digestOf_injective h, fun h => h ▸ rfl⟩

/-- The prover is injective. -/
theorem certify_injective : Function.Injective certify := fun _ _ h =>
  digestOf_injective (congrArg Certificate.digest h)

/-- Two artifacts get the same certificate iff they are equal. -/
theorem certify_inj_iff {a b : Artifact} : certify a = certify b ↔ a = b :=
  ⟨fun h => certify_injective h, fun h => h ▸ rfl⟩

/-- **Soundness and completeness of the isolation engine's integrity check.**

Given the certificate produced for the original artifact, the verifier's `reprove` step
succeeds on a received artifact if and only if that artifact is untampered:

* (⇐, completeness) an untampered artifact always reproves successfully;
* (⇒, soundness) any artifact that reproves successfully is bit-for-bit the original. -/
theorem reprove_matches_iff_untampered (orig recv : Artifact) :
    reprove recv (certify orig) = true ↔ Untampered orig recv := by
  simp only [reprove, Untampered, decide_eq_true_iff]
  exact certify_inj_iff

/-- Restatement on sealed bundles: with the certificate delivered intact, the received
bundle passes verification iff its artifact was not tampered with. -/
theorem reprove_sealBundle_iff_untampered (orig recv : Artifact) :
    reprove recv (sealBundle orig).2 = true ↔ Untampered orig recv :=
  reprove_matches_iff_untampered orig recv

/-- Completeness: a genuinely sealed bundle always verifies. -/
theorem reprove_sealBundle_self (a : Artifact) : reprove (sealBundle a).1 (sealBundle a).2 = true := by
  simp [reprove, sealBundle]

/-- Soundness, contrapositive form: any tampering with the artifact is detected. -/
theorem reprove_eq_false_of_tampered {orig recv : Artifact} (h : recv ≠ orig) :
    reprove recv (certify orig) = false := by
  have : ¬ (reprove recv (certify orig) = true) := by
    rw [reprove_matches_iff_untampered]
    exact h
  simpa using this

end PCA.Cert

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

