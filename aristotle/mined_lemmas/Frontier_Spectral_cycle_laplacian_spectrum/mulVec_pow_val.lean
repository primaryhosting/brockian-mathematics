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

lemma mulVec_pow_val (hn : 3 ≤ n) {ζ : ℂ} (hζ : ζ ^ n = 1) (i : ZMod n) :
    (cycleLaplacian n *ᵥ fun j => ζ ^ j.val) i = (2 - ζ - ζ⁻¹) * ζ ^ i.val := by
  have hζ0 : ζ ≠ 0 := ne_zero_of_pow_eq_one hζ
  have hsucc : ∀ a : ZMod n, ζ ^ (a + 1).val = ζ ^ a.val * ζ := by
    intro a
    rw [pow_val_add hζ, val_one_eq hn, pow_one]
  have hpred : ζ ^ (i - 1).val = ζ ^ i.val * ζ⁻¹ := by
    have h := hsucc (i - 1)
    rw [sub_add_cancel] at h
    rw [h, mul_assoc, mul_inv_cancel₀ hζ0, mul_one]
  rw [cycleLaplacian_mulVec hn]
  rw [hsucc i, hpred]
  ring

/-- The `ζ`-Fourier component of a vector `v`: `∑_m ζ^(-m) v(j + m)`. -/
