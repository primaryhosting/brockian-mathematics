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

def grants (p : Params G L) (rootPk : List UInt8) (sc : SignedCert)
    (subj res : List UInt8) : Bool :=
  accepts p rootPk sc && (sc.cert.subject == subj) && decide (res ∈ sc.cert.caps)

end Engine

section EngineTheorems

open Engine

variable {G : Type*} {L : ℕ} [AddCommGroup G] [Module (ZMod L) G] [DecidableEq G] [NeZero L]
variable (p : Params G L)

/-- **Engine completeness.** A certificate signed by the root authority (secret
scalar `a`, nonce `r`) is accepted, and the engine grants its subject access to
every resource the certificate lists. -/
