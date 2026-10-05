import Mathlib
/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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

open Finset ZMod

/-- The Laplacian matrix of the cycle graph `C n` on the vertex set `ZMod n`:
diagonal entries `2` (each vertex has degree `2`), and `-1` in position `(i, j)`
whenever `j = i + 1` or `j = i - 1`. -/

lemma dft_parseval (u : ZMod N → ℂ) :
    ∑ k : ZMod N, ‖𝓕 u k‖ ^ 2 = (N : ℝ) * ∑ j : ZMod N, ‖u j‖ ^ 2 := by
  have main : ∑ k : ZMod N, (𝓕 u k) * (starRingEnd ℂ) (𝓕 u k)
      = (N : ℂ) * ∑ j : ZMod N, u j * (starRingEnd ℂ) (u j) := by
    calc ∑ k : ZMod N, (𝓕 u k) * (starRingEnd ℂ) (𝓕 u k)
        = ∑ k : ZMod N, ∑ j : ZMod N, ∑ l : ZMod N,
            (u j * (starRingEnd ℂ) (u l)) * ZMod.stdAddChar ((l - j) * k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [ZMod.dft_apply]
          simp only [smul_eq_mul, map_sum, map_mul, conj_stdAddChar]
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
          rw [show ((l - j) * k) = (-(j * k)) + (-(-(l * k))) by ring, AddChar.map_add_eq_mul]
          ring
      _ = ∑ j : ZMod N, ∑ l : ZMod N, (u j * (starRingEnd ℂ) (u l)) *
            ∑ k : ZMod N, ZMod.stdAddChar ((l - j) * k) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ => (Finset.mul_sum _ _ _).symm
      _ = (N : ℂ) * ∑ j : ZMod N, u j * (starRingEnd ℂ) (u j) := by
          simp only [sum_stdAddChar_mul, sub_eq_zero]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_eq_single j]
          · simp; ring
          · intro l _ hl; simp [hl]
          · simp
  have hcast : ((∑ k : ZMod N, ‖𝓕 u k‖ ^ 2 : ℝ) : ℂ)
      = (((N : ℝ) * ∑ j : ZMod N, ‖u j‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_natCast]
    simpa only [Complex.mul_conj, Complex.normSq_eq_norm_sq] using main
  exact_mod_cast hcast

/-- The discrete Fourier transform turns the cyclic difference into multiplication
by `1 - χ(k)`. -/
