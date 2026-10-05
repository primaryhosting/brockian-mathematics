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

theorem listDigest_injective : Function.Injective listDigest := by
  rintro ⟨ca, pa⟩ ⟨cb, pb⟩ h
  simp only [listDigest, List.cons.injEq] at h
  obtain ⟨hlen, happ⟩ := h
  obtain ⟨hc, hp⟩ := List.append_inj happ hlen
  simp only [Artifact.mk.injEq]
  exact ⟨hc, hp⟩

/-- The main theorem instantiated at a concrete digest: no hypotheses remain, so the
statement is not vacuous. -/
