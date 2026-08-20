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

theorem ed25519_special_soundness [Fact (Nat.Prime L)] {A R : G} {S₁ S₂ c₁ c₂ : ZMod L}
    (h₁ : S₁ • p.B = R + c₁ • A) (h₂ : S₂ • p.B = R + c₂ • A) (hne : c₁ ≠ c₂) :
    A = ((S₁ - S₂) * (c₁ - c₂)⁻¹) • p.B := by
  have hc : c₁ - c₂ ≠ 0 := sub_ne_zero_of_ne hne
  have h1 : (S₁ - S₂) • p.B = (c₁ - c₂) • A := by
    rw [sub_smul, h₁, h₂, sub_smul]
    abel
  have h2 : ((S₁ - S₂) * (c₁ - c₂)⁻¹) • p.B = ((c₁ - c₂)⁻¹ * (c₁ - c₂)) • A := by
    rw [mul_comm (S₁ - S₂) (c₁ - c₂)⁻¹, mul_smul, h1, mul_smul]
  rw [inv_mul_cancel₀ hc, one_smul] at h2
  exact h2.symm

/-- **Strong unforgeability at the byte level (non-malleability).** Two accepted
signatures on the same message under the same key that share the same nonce
component are equal as byte strings. In particular the scalar `S` cannot be
mauled (e.g. by adding `L`) without breaking verification. -/
