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

@[simp] theorem length_natToLe (n k : ℕ) : (natToLe n k).length = k := by
  induction k generalizing n with
  | zero => simp
  | succ k ih => simp [ih]

