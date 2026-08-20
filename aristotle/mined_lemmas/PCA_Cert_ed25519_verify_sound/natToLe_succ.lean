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

@[simp] theorem natToLe_succ (n k : ℕ) :
    natToLe n (k + 1) = UInt8.ofNat (n % 256) :: natToLe (n / 256) k := rfl

