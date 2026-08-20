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

theorem encScalar_decScalar [NeZero L] {bs : List UInt8} {s : ZMod L}
    (h : decScalar L bs = some s) : encScalar L s = bs := by
  unfold decScalar at h
  split at h
  · rename_i hc
    obtain ⟨hlen, hlt⟩ := hc
    have hs : s = ((leToNat bs : ℕ) : ZMod L) := by simpa using h.symm
    have hvs : s.val = leToNat bs := by
      rw [hs, ZMod.val_natCast_of_lt hlt]
    rw [encScalar, hvs, ← hlen, natToLe_leToNat]
  · exact absurd h (by simp)

end Scalars

/-- Static parameters of the Ed25519-style scheme: a prime-order group with a
base point, a canonical point encoding and a hash function. -/
structure Params (G : Type*) (L : ℕ) [AddCommGroup G] [Module (ZMod L) G] where
  /-- The base point. -/
  B : G
  /-- `B` has exact order `L`: no nonzero scalar kills it. -/
  hB : ∀ s : ZMod L, s • B = 0 → s = 0
  /-- Scalars fit in 32 bytes. -/
  hL : L ≤ 2 ^ 256
  /-- Point encoding. -/
  encPt : G → List UInt8
  /-- Encoded points are 32 bytes long. -/
  encPt_length : ∀ P, (encPt P).length = 32
  /-- Point decoding. -/
  decPt : List UInt8 → Option G
  /-- Decoding an encoded point recovers it. -/
  decPt_encPt : ∀ P, decPt (encPt P) = some P
  /-- The encoding is canonical: at most one byte string decodes to a given point. -/
  encPt_decPt : ∀ bs P, decPt bs = some P → encPt P = bs
  /-- The hash function, applied to (encoded nonce, encoded public key, message). -/
  H : List UInt8 → List UInt8 → List UInt8 → ZMod L

namespace Params

variable {G : Type*} {L : ℕ} [AddCommGroup G] [Module (ZMod L) G] [DecidableEq G]
variable (p : Params G L)

/-- The public key associated with the secret scalar `a`. -/
