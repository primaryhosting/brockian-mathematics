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

def demoParams : Params (ZMod 7) 7 := Params.ofZMod 7 (by norm_num) demoH

/-- A certificate for subject `[1]` granting access to resources `[2]` and `[3]`. -/
