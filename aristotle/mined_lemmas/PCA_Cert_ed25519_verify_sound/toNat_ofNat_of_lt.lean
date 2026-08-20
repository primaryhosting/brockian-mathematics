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

theorem toNat_ofNat_of_lt {n : ℕ} (h : n < 256) : (UInt8.ofNat n).toNat = n := by
  simp [Nat.mod_eq_of_lt h]

