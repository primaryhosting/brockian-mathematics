/-
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command; the module docstring below
-- repeats the header verbatim.)
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

open Matrix Polynomial

/-- The cyclic shift matrix on `ZMod n`: `shiftM n a i j = 1` exactly when `i - j = a`. -/

lemma mem_spectrum_of_mulVec_eq (M : Matrix (ZMod n) (ZMod n) ℂ) (mu : ℂ) (v : ZMod n → ℂ)
    (hv : v ≠ 0) (h : M *ᵥ v = mu • v) : mu ∈ spectrum ℂ M := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨v, hv, ?_⟩
  have halg : (algebraMap ℂ (Matrix (ZMod n) (ZMod n) ℂ)) mu = mu • (1 : Matrix _ _ ℂ) :=
    Algebra.algebraMap_eq_smul_one mu
  rw [Matrix.sub_mulVec, h, halg, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]

/-- Every `n`-th root of unity is an eigenvalue of the cyclic shift, with the discrete
Fourier eigenvector `j ↦ z ^ j`. -/
