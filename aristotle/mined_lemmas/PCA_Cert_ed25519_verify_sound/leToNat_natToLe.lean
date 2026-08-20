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

theorem leToNat_natToLe (n k : ℕ) : leToNat (natToLe n k) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
      have hmod : (UInt8.ofNat (n % 256)).toNat = n % 256 :=
        toNat_ofNat_of_lt (Nat.mod_lt _ (by norm_num))
      rw [natToLe_succ, leToNat_cons, hmod, ih]
      have : n % 256 ^ (k + 1) = n % 256 + 256 * (n / 256 % 256 ^ k) := by
        rw [pow_succ', Nat.mod_mul]
      omega

