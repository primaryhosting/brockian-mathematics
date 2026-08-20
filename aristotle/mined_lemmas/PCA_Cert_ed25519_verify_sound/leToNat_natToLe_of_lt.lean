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

theorem leToNat_natToLe_of_lt {n k : ℕ} (h : n < 256 ^ k) : leToNat (natToLe n k) = n := by
  rw [leToNat_natToLe, Nat.mod_eq_of_lt h]

/-- Encoding the value of a byte string recovers the byte string. -/
