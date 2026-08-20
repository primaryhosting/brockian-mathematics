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

def pk (a : ZMod L) : List UInt8 := p.encPt (a • p.B)

/-- Ed25519 verification of a 64-byte signature `sigb` on `msg` under the
encoded public key `pkb`. -/
