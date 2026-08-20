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

open Complex Matrix ZMod AddChar Finset

/-- The generating vector of the cycle Laplacian: `2` at `0`, `-1` at `±1`, `0` elsewhere. -/

lemma laplacian_mul_fourier (hn : 3 ≤ n) :
    cycleLaplacian n * fourierMat n = fourierMat n * Matrix.diagonal (cycleEigen n) := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have re : ∑ j : ZMod n, cycleLaplacian n i j * fourierMat n j k
      = ∑ d : ZMod n, cycleLapVec n d * ZMod.stdAddChar ((i - d) * k) := by
    refine (Fintype.sum_equiv (Equiv.subLeft i) _ _ ?_).symm
    intro d
    simp only [Equiv.subLeft_apply, cycleLaplacian, Matrix.circulant_apply, fourierMat,
      Matrix.of_apply]
    congr 2
    ring
  rw [re, sum_cycleLapVec_mul hn]
  simp only [fourierMat, Matrix.of_apply, cycleEigen]
  have e1 : ZMod.stdAddChar ((i - 1) * k) = ZMod.stdAddChar (i * k) * ZMod.stdAddChar (-k) := by
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  have e2 : ZMod.stdAddChar ((i - -1) * k) = ZMod.stdAddChar (i * k) * ZMod.stdAddChar k := by
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  rw [e1, e2, sub_zero]
  ring

/-- The eigenvalues are `2 - 2 cos (2 π k / n)`. -/
