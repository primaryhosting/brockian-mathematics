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

lemma fourierComp_shift (hn : 3 ≤ n) {ζ : ℂ} (hζ : ζ ^ n = 1) (v : ZMod n → ℂ) (j : ZMod n) :
    fourierComp ζ v (j + 1) = ζ * fourierComp ζ v j := by
  have hζ0 : ζ ≠ 0 := ne_zero_of_pow_eq_one hζ
  have hreindex : ∀ F : ZMod n → ℂ, ∑ m : ZMod n, F m = ∑ m : ZMod n, F (m + 1) :=
    fun F => (Fintype.sum_equiv (Equiv.addRight (1 : ZMod n)) _ _ (fun _ => rfl)).symm
  simp only [fourierComp, Finset.mul_sum]
  rw [hreindex fun m => ζ * ((ζ ^ m.val)⁻¹ * v (j + m))]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hval : ζ ^ (m + 1).val = ζ ^ m.val * ζ := by
    rw [pow_val_add hζ, val_one_eq hn, pow_one]
  have hjm : j + 1 + m = j + m + 1 := by ring
  rw [hval, hjm]
  have hne : ζ ^ m.val ≠ 0 := pow_ne_zero _ hζ0
  field_simp
  rw [add_assoc]

/-- Taking Fourier components preserves the eigenvector equation for the Laplacian. -/
