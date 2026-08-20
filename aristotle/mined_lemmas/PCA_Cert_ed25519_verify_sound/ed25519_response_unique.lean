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

theorem ed25519_response_unique {pkb msg sigb sigb' : List UInt8}
    (h : p.verify pkb msg sigb = true) (h' : p.verify pkb msg sigb' = true)
    (hR : sigb.take 32 = sigb'.take 32) : sigb = sigb' := by
  rw [Params.verify_iff] at h h'
  obtain ⟨hlen, A, R, S, hA, hRd, hS, heq⟩ := h
  obtain ⟨hlen', A', R', S', hA', hRd', hS', heq'⟩ := h'
  rw [hA] at hA'
  rw [← hR, hRd] at hRd'
  rw [← hR] at heq'
  cases hA'; cases hRd'
  have hSS : S = S' := by
    have hz : (S - S') • p.B = 0 := by
      rw [sub_smul, heq, heq']
      abel
    exact sub_eq_zero.mp (p.hB _ hz)
  have hSb : encScalar L S = sigb.drop 32 := encScalar_decScalar hS
  have hSb' : encScalar L S' = sigb'.drop 32 := encScalar_decScalar hS'
  have hdrop : sigb.drop 32 = sigb'.drop 32 := by rw [← hSb, ← hSb', hSS]
  calc sigb = sigb.take 32 ++ sigb.drop 32 := (List.take_append_drop _ _).symm
    _ = sigb'.take 32 ++ sigb'.drop 32 := by rw [hR, hdrop]
    _ = sigb' := List.take_append_drop _ _

omit [NeZero L] in
/-- **Non-canonical scalars are rejected.** If the scalar half of the signature
encodes a value `≥ L` (the classical Ed25519 malleability trick of adding the
group order), verification fails. -/
