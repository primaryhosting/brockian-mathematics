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

theorem leToNat_lt (bs : List UInt8) : leToNat bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      have hb : b.toNat < 256 := UInt8.toNat_lt b
      simp only [leToNat_cons, List.length_cons, pow_succ]
      omega

/-- Decoding the little-endian encoding of `n` recovers `n` modulo `256 ^ k`. -/
