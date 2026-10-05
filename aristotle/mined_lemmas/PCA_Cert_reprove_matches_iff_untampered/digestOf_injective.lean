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

theorem digestOf_injective : Function.Injective digestOf := by
  rintro ⟨c₁, d₁⟩ ⟨c₂, d₂⟩ h
  simp only [digestOf, List.cons.injEq] at h
  obtain ⟨hlen, happ⟩ := h
  obtain ⟨hc, hd⟩ := List.append_inj happ hlen
  simp [hc, hd]

/-- Two artifacts have the same digest iff they are equal. -/
