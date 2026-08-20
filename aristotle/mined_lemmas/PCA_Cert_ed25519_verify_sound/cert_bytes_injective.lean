import Mathlib

/-!
# Little-endian byte strings

Basic infrastructure for the Ed25519 certificate model: conversion between
natural numbers and fixed-width little-endian byte strings, together with the
round-trip and injectivity lemmas that make byte-level canonicality arguments
possible.
-/

namespace PCA

/-- Value of a little-endian byte string (least significant byte first). -/

theorem cert_bytes_injective {c c' : CapCert} (hc : c.WF) (hc' : c'.WF)
    (h : c.bytes = c'.bytes) : c = c' := by
  obtain ⟨hs, hn, hr⟩ := hc
  obtain ⟨hs', hn', hr'⟩ := hc'
  have h' : encBytes c.subject ++ (natToLe c.caps.length 4 ++ encList c.caps) =
      encBytes c'.subject ++ (natToLe c'.caps.length 4 ++ encList c'.caps) := by
    simpa [CapCert.bytes, List.append_assoc] using h
  obtain ⟨hsub, hrest⟩ := encBytes_inj_append hs hs' h'
  obtain ⟨hpre, htail⟩ :=
    List.append_inj hrest (by rw [length_natToLe, length_natToLe])
  have hlen : c.caps.length = c'.caps.length := by
    have := congrArg leToNat hpre
    rwa [leToNat_natToLe_of_lt hn, leToNat_natToLe_of_lt hn'] at this
  obtain ⟨hcaps, -⟩ := encList_inj_append (x := []) (y := []) hr hr' hlen (by simpa using htail)
  cases c; cases c'
  simp_all

/-! ## The engine -/

namespace Engine

variable {G : Type*} {L : ℕ} [AddCommGroup G] [Module (ZMod L) G] [DecidableEq G]

/-- A certificate together with the authority's signature on it. -/
structure SignedCert where
  /-- The certificate. -/
  cert : CapCert
  /-- The 64-byte Ed25519 signature over `cert.bytes`. -/
  sig : List UInt8

/-- The engine accepts a signed certificate when the signature verifies under
the root public key. -/
