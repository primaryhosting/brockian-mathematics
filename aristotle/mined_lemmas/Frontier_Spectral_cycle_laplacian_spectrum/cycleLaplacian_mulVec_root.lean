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

variable {n : ℕ} [NeZero n]

/-- The cyclic shift matrix on `ZMod n`: `shift n i j = 1` iff `i - j = 1`. -/

lemma cycleLaplacian_mulVec_root (hn : 3 ≤ n) {ζ : ℂ} (hζ : ζ ^ n = 1) :
    cycleLaplacian n *ᵥ (fun i : ZMod n => ζ ^ i.val)
      = (2 - (ζ + ζ⁻¹)) • (fun i : ZMod n => ζ ^ i.val) := by
  have hne : Fact (1 < n) := ⟨by omega⟩
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h, zero_pow (by omega)] at hζ; exact zero_ne_one hζ
  rw [cycleLaplacian_mulVec hn]
  funext i
  have hadd : ζ ^ (i + 1).val = ζ ^ i.val * ζ := by
    rw [ZMod.val_add, ZMod.val_one, pow_mod_eq hζ, pow_succ]
  have hsub : ζ ^ (i - 1).val = ζ⁻¹ * ζ ^ i.val := by
    have key : i.val = ((i - 1).val + 1) % n := by
      have hi : i = (i - 1) + 1 := by ring
      conv_lhs => rw [hi]
      rw [ZMod.val_add, ZMod.val_one]
    rw [key, pow_mod_eq hζ, pow_succ]
    field_simp
  show 2 * ζ ^ i.val - ζ ^ (i - 1).val - ζ ^ (i + 1).val = _
  rw [hadd, hsub]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The discrete Fourier vectors `v k j = exp (2 π I k j / n)` are eigenvectors of the cycle
Laplacian, with eigenvalue `2 - 2 cos (2 π k / n)`. -/
