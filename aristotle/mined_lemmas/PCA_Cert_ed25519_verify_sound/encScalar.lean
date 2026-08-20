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

def encScalar (s : ZMod L) : List UInt8 := natToLe s.val 32

/-- Canonical scalar decoding: 32 little-endian bytes whose value is `< L`.
Non-canonical encodings (value `≥ L`) are rejected. -/
