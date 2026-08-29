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

lemma fourierComp_mulVec (hn : 3 ≤ n) {ζ μ : ℂ} (v : ZMod n → ℂ)
    (hv : cycleLaplacian n *ᵥ v = μ • v) (j : ZMod n) :
    (cycleLaplacian n *ᵥ fourierComp ζ v) j = μ * fourierComp ζ v j := by
  rw [cycleLaplacian_mulVec hn]
  simp only [fourierComp, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := congrFun hv (j + m)
  rw [cycleLaplacian_mulVec hn] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  have e1 : j + 1 + m = j + m + 1 := by ring
  have e2 : j - 1 + m = j + m - 1 := by ring
  rw [e1, e2]
  linear_combination (ζ ^ m.val)⁻¹ * h

/-- The Fourier components over all `n`-th roots of unity reconstruct the vector. -/
