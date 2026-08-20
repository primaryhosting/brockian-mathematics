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

theorem engine_confinement {rootPk : List UInt8} {issued : Set CapCert}
    {allowed : Set (List UInt8)}
    (hWF : ∀ c ∈ issued, c.WF)
    (hEUF : ∀ msg sig, p.verify rootPk msg sig = true → ∃ c ∈ issued, c.bytes = msg)
    {subj : List UInt8}
    (hpolicy : ∀ c ∈ issued, c.subject = subj → ∀ r ∈ c.caps, r ∈ allowed)
    {sc : SignedCert} {res : List UInt8} (hsc : sc.cert.WF)
    (hgrant : grants p rootPk sc subj res = true) :
    res ∈ allowed := by
  obtain ⟨c, hcmem, hsubj, hres⟩ := engine_sound p hWF hEUF hsc hgrant
  exact hpolicy c hcmem hsubj res hres

end EngineTheorems

end Cert
end PCA

