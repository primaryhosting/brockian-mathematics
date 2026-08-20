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

def decScalar (bs : List UInt8) : Option (ZMod L) :=
  if bs.length = 32 ∧ leToNat bs < L then some ((leToNat bs : ZMod L)) else none

