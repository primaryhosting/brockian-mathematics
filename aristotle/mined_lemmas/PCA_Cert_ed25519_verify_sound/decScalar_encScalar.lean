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

theorem decScalar_encScalar [NeZero L] (hL : L ≤ 2 ^ 256) (s : ZMod L) :
    decScalar L (encScalar L s) = some s := by
  have hval : s.val < L := ZMod.val_lt s
  have h256 : (256 : ℕ) ^ 32 = 2 ^ 256 := by norm_num
  have hlt : s.val < 256 ^ 32 := by omega
  have hval' : leToNat (encScalar L s) = s.val := by
    rw [encScalar]; exact leToNat_natToLe_of_lt hlt
  have hlen : (encScalar L s).length = 32 := length_encScalar L s
  unfold decScalar
  rw [if_pos ⟨hlen, by rw [hval']; exact hval⟩, hval', ZMod.natCast_zmod_val]

/-- Decoding is canonical: a byte string that decodes to `s` *is* the encoding of `s`. -/
