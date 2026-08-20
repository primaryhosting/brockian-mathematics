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

theorem leToNat_injective {bs cs : List UInt8} (hlen : bs.length = cs.length)
    (h : leToNat bs = leToNat cs) : bs = cs := by
  have := natToLe_leToNat bs
  rw [h, hlen, natToLe_leToNat] at this
  exact this.symm

end PCA

import RequestProject.Engine

/-!
# A worked instance of the model

A small but complete instantiation of the certificate model, demonstrating that
the assumptions bundled in `PCA.Cert.Params` are satisfiable and that the
engine's grant predicate really does fire on honestly issued certificates
(so the soundness statements are not vacuous).
-/

namespace PCA
namespace Cert
namespace Demo

/-- A toy hash function. -/
