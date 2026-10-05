/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Cert

/-- An *artifact* handled by the isolation engine: the app's code together with the
isolation policy it is supposed to run under. -/
structure Artifact where
  /-- The app's code, as a sequence of opcodes. -/
  code : List Nat
  /-- The isolation policy the app was certified against. -/
  policy : List Nat
  deriving DecidableEq, Repr

/-- A *certificate*, as shipped alongside a proof-carrying app: it binds the artifact
that was checked at issuance time to a digest value of type `D`. -/
structure Certificate (D : Type u) where
  /-- The digest of the artifact recorded when the certificate was issued. -/
  digest : D
  deriving Repr

/-- Issuing a certificate for an artifact: record its digest. -/
def issue {D : Type u} (dg : Artifact → D) (a : Artifact) : Certificate D :=
  ⟨dg a⟩

/-- Re-proving: the isolation engine recomputes the digest of the artifact it is about
to load and compares it with the digest bound in the certificate. -/
def reprove {D : Type u} [DecidableEq D] (dg : Artifact → D)
    (c : Certificate D) (a : Artifact) : Bool :=
  decide (dg a = c.digest)

/-- An artifact is *untampered* with respect to the artifact that was originally
certified exactly when it is that same artifact. -/
def Untampered (orig a : Artifact) : Prop := a = orig

instance (orig a : Artifact) : Decidable (Untampered orig a) :=
  inferInstanceAs (Decidable (a = orig))

/-- **Soundness and completeness of the re-proving check.**

For a collision-free (injective) digest function, the isolation engine's re-proof of the
certificate issued for `orig` succeeds on the artifact `a` it is about to load if and
only if `a` has not been tampered with.

The forward direction is *soundness* (a passing re-proof guarantees the loaded artifact
is exactly the certified one); the backward direction is *completeness* (an untampered
artifact is never rejected). -/
theorem reprove_matches_iff_untampered {D : Type u} [DecidableEq D] (dg : Artifact → D)
    (hdg : Function.Injective dg) (orig a : Artifact) :
    reprove dg (issue dg orig) a = true ↔ Untampered orig a := by
  constructor
  · intro h
    have h' : dg a = dg orig := of_decide_eq_true h
    exact hdg h'
  · intro h
    have : dg a = dg orig := congrArg dg h
    exact decide_eq_true this

/-- Contrapositive form: any tampering with the artifact is detected. -/
theorem reprove_eq_false_of_tampered {D : Type u} [DecidableEq D] (dg : Artifact → D)
    (hdg : Function.Injective dg) (orig a : Artifact) (h : ¬ Untampered orig a) :
    reprove dg (issue dg orig) a = false := by
  cases hb : reprove dg (issue dg orig) a with
  | false => rfl
  | true => exact absurd ((reprove_matches_iff_untampered dg hdg orig a).mp hb) h

/-- A concrete collision-free digest: the code length, followed by the code and the
policy. Knowing the length of the code lets one recover both components. -/
def listDigest (a : Artifact) : List Nat :=
  a.code.length :: (a.code ++ a.policy)

theorem listDigest_injective : Function.Injective listDigest := by
  rintro ⟨ca, pa⟩ ⟨cb, pb⟩ h
  simp only [listDigest, List.cons.injEq] at h
  obtain ⟨hlen, happ⟩ := h
  obtain ⟨hc, hp⟩ := List.append_inj happ hlen
  simp only [Artifact.mk.injEq]
  exact ⟨hc, hp⟩

/-- The main theorem instantiated at a concrete digest: no hypotheses remain, so the
statement is not vacuous. -/
theorem reprove_listDigest_iff_untampered (orig a : Artifact) :
    reprove listDigest (issue listDigest orig) a = true ↔ Untampered orig a :=
  reprove_matches_iff_untampered listDigest listDigest_injective orig a

/-- The isolation engine loads an artifact only when its certificate re-proves. -/
def loads {D : Type u} [DecidableEq D] (dg : Artifact → D)
    (c : Certificate D) (a : Artifact) : Prop :=
  reprove dg c a = true

/-- End-to-end statement for the engine: with a collision-free digest, the engine loads
exactly the untampered artifacts. -/
theorem loads_iff_untampered {D : Type u} [DecidableEq D] (dg : Artifact → D)
    (hdg : Function.Injective dg) (orig a : Artifact) :
    loads dg (issue dg orig) a ↔ Untampered orig a :=
  reprove_matches_iff_untampered dg hdg orig a

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

