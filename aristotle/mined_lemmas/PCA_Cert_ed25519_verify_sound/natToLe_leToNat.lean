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

theorem natToLe_leToNat (bs : List UInt8) : natToLe (leToNat bs) bs.length = bs := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      have hb : b.toNat < 256 := UInt8.toNat_lt b
      have h1 : (b.toNat + 256 * leToNat bs) % 256 = b.toNat := by omega
      have h2 : (b.toNat + 256 * leToNat bs) / 256 = leToNat bs := by omega
      simp only [List.length_cons, natToLe_succ, leToNat_cons, h1, h2, ih,
        List.cons.injEq, and_true]
      exact UInt8.ofNat_toNat

/-- Byte strings of equal length with equal values are equal. -/
