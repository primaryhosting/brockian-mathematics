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

theorem engine_isolation {rootPk : List UInt8} {issued : Set CapCert}
    (hWF : ∀ c ∈ issued, c.WF)
    (hEUF : ∀ msg sig, p.verify rootPk msg sig = true → ∃ c ∈ issued, c.bytes = msg)
    {subj res : List UInt8}
    (hnone : ∀ c ∈ issued, c.subject = subj → res ∉ c.caps)
    (sc : SignedCert) (hsc : sc.cert.WF) :
    grants p rootPk sc subj res = false := by
  cases hg : grants p rootPk sc subj res with
  | false => rfl
  | true =>
      obtain ⟨c, hcmem, hsubj, hres⟩ := engine_sound p hWF hEUF hsc hg
      exact (hnone c hcmem hsubj hres).elim

omit [NeZero L] in
/-- **Confinement.** If every issued certificate for `subj` lists only resources
inside the policy set `allowed`, then every access the engine grants to `subj`
stays inside `allowed`. -/
