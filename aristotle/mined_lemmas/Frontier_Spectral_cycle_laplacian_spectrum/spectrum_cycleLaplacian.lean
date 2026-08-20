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

lemma spectrum_cycleLaplacian (hn : 3 ≤ n) :
    spectrum ℂ (cycleLaplacian n) = Set.range (cycleEigen n) := by
  set u : (Matrix (ZMod n) (ZMod n) ℂ)ˣ :=
    ⟨fourierMat n, fourierMatInv n, fourier_mul_inv, inv_mul_fourier⟩ with hu
  have hconj : cycleLaplacian n
      = (u : Matrix (ZMod n) (ZMod n) ℂ) * Matrix.diagonal (cycleEigen n)
        * ((u⁻¹ : (Matrix (ZMod n) (ZMod n) ℂ)ˣ) : Matrix (ZMod n) (ZMod n) ℂ) :=
    laplacian_eq_conj hn
  rw [hconj, spectrum.units_conjugate, _root_.spectrum_diagonal]

end

/-- **Spectrum of the cycle Laplacian.** For `n ≥ 3`, the eigenvalues of the graph Laplacian
of the cycle graph `C n` (modelled as the `n × n` circulant matrix with diagonal `2` and `-1`
on the two cyclic off-diagonals, diagonalized by the discrete Fourier eigenvectors
`v k j = exp (2 π I k j / n)`) are exactly the numbers `2 - 2 cos (2 π k / n)` for
`k = 0, …, n - 1`. -/
