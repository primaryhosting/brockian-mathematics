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

theorem engine_sound {rootPk : List UInt8} {issued : Set CapCert}
    (hWF : ∀ c ∈ issued, c.WF)
    (hEUF : ∀ msg sig, p.verify rootPk msg sig = true → ∃ c ∈ issued, c.bytes = msg)
    {sc : SignedCert} {subj res : List UInt8}
    (hsc : sc.cert.WF)
    (hgrant : grants p rootPk sc subj res = true) :
    ∃ c ∈ issued, c.subject = subj ∧ res ∈ c.caps := by
  unfold grants accepts at hgrant
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hgrant
  obtain ⟨⟨hver, hsubj⟩, hres⟩ := hgrant
  obtain ⟨c, hcmem, hcb⟩ := hEUF _ _ hver
  have hceq : c = sc.cert := cert_bytes_injective (hWF c hcmem) hsc hcb
  rw [hceq] at hcmem
  exact ⟨sc.cert, hcmem, hsubj, hres⟩

omit [NeZero L] in
/-- **Isolation.** Under the same unforgeability assumption, if no issued
certificate authorizes `subj` to use `res`, then the engine denies every
presented certificate: the subject is confined. -/
