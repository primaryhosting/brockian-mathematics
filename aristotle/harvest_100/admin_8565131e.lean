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
def encodeField (l : List Nat) : List Nat := l.length :: l

/-- The digest (serialisation) of an artifact: the concatenation of the
length-prefixed encodings of its three components. -/
def digest (a : Artifact) : List Nat :=
  encodeField a.code ++ (encodeField a.config ++ encodeField a.policy)

/-- A certificate carried by a proof-carrying app: it records the digest of the
artifact for which the accompanying proof was produced. -/
structure Certificate where
  recorded : List Nat
  deriving DecidableEq

/-- The certificate issued for an artifact. -/
def issue (a : Artifact) : Certificate := ⟨digest a⟩

/-- Re-proving (re-checking) a certificate against a presented artifact: the
engine recomputes the digest of what it is about to run and compares it with the
digest recorded in the certificate. -/
def reprove (c : Certificate) (a : Artifact) : Bool :=
  decide (digest a = c.recorded)

/-- The presented artifact is untampered when it is exactly the artifact the
certificate was issued for. -/
def Untampered (orig a : Artifact) : Prop := a = orig

/-- A concatenation of a length-prefixed field with a remainder splits uniquely. -/
theorem encodeField_append_inj {l₁ l₂ x y : List Nat}
    (h : encodeField l₁ ++ x = encodeField l₂ ++ y) : l₁ = l₂ ∧ x = y := by
  simp only [encodeField, List.cons_append, List.cons.injEq] at h
  exact List.append_inj h.2 h.1

/-- The digest is injective: distinct artifacts have distinct digests. -/
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
theorem reprove_matches_iff_untampered (orig a : Artifact) :
    reprove (issue orig) a = true ↔ Untampered orig a := by
  constructor
  · intro h
    have hd : digest a = digest orig := by
      simpa [reprove, issue] using h
    exact digest_injective hd
  · intro h
    subst h
    simp [reprove, issue]

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

