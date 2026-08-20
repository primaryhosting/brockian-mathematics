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

def demoH : List UInt8 → List UInt8 → List UInt8 → ZMod 7 := fun _ _ _ => 3

/-- A toy instance of the scheme, over the prime-order group `ZMod 7`. -/
