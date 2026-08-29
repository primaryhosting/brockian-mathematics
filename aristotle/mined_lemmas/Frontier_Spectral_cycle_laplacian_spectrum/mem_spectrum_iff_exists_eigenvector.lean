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
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Complex Matrix

/-- The graph Laplacian of the cycle graph `C n`, as the `n × n` circulant matrix with
diagonal `2` and `-1` on the two cyclic off-diagonals (indices are taken in `ZMod n`). -/

lemma mem_spectrum_iff_exists_eigenvector {m : Type} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℂ) (μ : ℂ) :
    μ ∈ spectrum ℂ M ↔ ∃ v : m → ℂ, v ≠ 0 ∧ M *ᵥ v = μ • v := by
  have hone : ∀ v : m → ℂ, ((μ • 1 : Matrix m m ℂ)) *ᵥ v = μ • v := by
    intro v; rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_ne_iff,
    ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv0, hv⟩
    rw [sub_mulVec, sub_eq_zero, Algebra.algebraMap_eq_smul_one, hone] at hv
    exact ⟨v, hv0, hv.symm⟩
  · rintro ⟨v, hv0, hv⟩
    refine ⟨v, hv0, ?_⟩
    rw [sub_mulVec, sub_eq_zero, Algebra.algebraMap_eq_smul_one, hone, hv]

/-- The same result phrased with the algebraic spectrum of the matrix. -/
