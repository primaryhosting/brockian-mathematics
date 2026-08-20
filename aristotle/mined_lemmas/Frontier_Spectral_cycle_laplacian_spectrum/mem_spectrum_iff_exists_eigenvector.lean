import Mathlib
/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Polynomial Matrix Complex

variable (n : ℕ) [NeZero n]

/-- The cyclic shift matrix on `ZMod n`: `(S *ᵥ v) i = v (i + 1)`. -/

lemma mem_spectrum_iff_exists_eigenvector (M : Matrix (ZMod n) (ZMod n) ℂ) (μ : ℂ) :
    μ ∈ spectrum ℂ M ↔ ∃ v : ZMod n → ℂ, v ≠ 0 ∧ M *ᵥ v = μ • v := by
  have key : ∀ v : ZMod n → ℂ,
      (algebraMap ℂ (Matrix (ZMod n) (ZMod n) ℂ) μ - M) *ᵥ v = μ • v - M *ᵥ v := by
    intro v
    rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_ne_iff,
    ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, by rw [key v, sub_eq_zero] at h; exact h.symm⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, by rw [key v, sub_eq_zero, h]⟩

