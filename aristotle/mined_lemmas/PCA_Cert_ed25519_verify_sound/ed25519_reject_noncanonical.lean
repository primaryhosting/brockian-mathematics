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

theorem ed25519_reject_noncanonical {pkb msg sigb : List UInt8}
    (h : L ≤ leToNat (sigb.drop 32)) : p.verify pkb msg sigb = false := by
  cases hv : p.verify pkb msg sigb with
  | false => rfl
  | true =>
      rw [Params.verify_iff] at hv
      obtain ⟨-, A, R, S, -, -, hS, -⟩ := hv
      unfold decScalar at hS
      rw [if_neg (fun hc => absurd hc.2 (by omega))] at hS
      exact absurd hS (by simp)

end Theorems

section Instantiation

/-- A concrete instantiation of the model: the group is the scalar field itself
with base point `1` and canonical little-endian encodings. This witnesses that
the assumptions bundled in `Params` are consistent (the model is not vacuous). -/
