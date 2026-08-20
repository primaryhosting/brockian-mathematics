import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Statement: A time-reversal-invariant half-integer-spin system has doubly degenerate levels (Kramers).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace Phys

/-- A vector and its image under an antiunitary time-reversal operator squaring to `-1`
are linearly independent (the algebraic heart of Kramers' theorem). -/

def spinHalfTimeReversal : (ℂ × ℂ) →ₗ⋆[ℂ] (ℂ × ℂ) where
  toFun p := (-(starRingEnd ℂ p.2), starRingEnd ℂ p.1)
  map_add' p q := by simp [Prod.ext_iff]; ring
  map_smul' c p := by simp

/-- The spin-1/2 time-reversal operator squares to `-1`, so the hypotheses of
`Phys.kramers_degeneracy` are satisfiable: the theorem is not vacuous. -/
