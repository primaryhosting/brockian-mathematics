/-
  CompactCriterion.lean — an abstract compactness criterion: an operator whose
  unit-ball image is uniformly approximable by finite-dimensional subspaces is
  a compact operator.
-/
import Mathlib

open Metric Filter

namespace Brockian.Weyl.OscillatorCompact

/-- An operator whose closed-unit-ball image is uniformly approximable by
finite-dimensional subspaces is a compact operator. -/

theorem resolvent_mem_closure_goodSet {z : ℂ} (hz : |z.im| = 1) (hz' : z.re = 0)
    {R : L2R →L[ℂ] L2R} (hR : RightResolvent harmonicOscillatorPMap.closure z R)
    (hsym : IsSymmetric harmonicOscillatorPMap.closure)
    (y : L2R) (hy : ‖y‖ ≤ 1) : R y ∈ closure (goodSet 2) := by
  obtain ⟨hmem, hval⟩ := hR y
  set v : (harmonicOscillatorPMap.closure).domain := ⟨R y, hmem⟩ with hv
  have hznorm : ‖z‖ = 1 := by
    have : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply]; ring
    have him : z.im ^ 2 = 1 := by
      have := hz
      nlinarith [abs_nonneg z.im, sq_abs z.im]
    have h0 : ‖z‖ ^ 2 = 1 := by rw [this, hz', him]; ring
    nlinarith [norm_nonneg z]
  -- the norm bound on `v`
  have hvnorm : ‖(v : L2R)‖ ≤ 1 := by
    have h := norm_le_norm_shifted hsym hz v
    rw [hval] at h
    linarith
  -- the Pythagorean identity
  have hTnorm : ‖harmonicOscillatorPMap.closure v‖ ≤ 1 := by
    have hre : (inner ℂ (harmonicOscillatorPMap.closure v) ((v : L2R))).im = 0 :=
      hsym.inner_self_im v
    have hexp := norm_sub_sq (𝕜 := ℂ) (harmonicOscillatorPMap.closure v) (z • (v : L2R))
    rw [inner_smul_right, norm_smul, hznorm] at hexp
    have hcross : RCLike.re (z * inner ℂ (harmonicOscillatorPMap.closure v) ((v : L2R))) = 0 := by
      show (z * inner ℂ (harmonicOscillatorPMap.closure v) ((v : L2R))).re = 0
      rw [Complex.mul_re, hre, hz']
      ring
    rw [hcross, hval] at hexp
    have hy2 : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
    have hnn := norm_nonneg (harmonicOscillatorPMap.closure v)
    nlinarith [norm_nonneg (v : L2R)]
  have := mem_closure_goodSet v hvnorm hTnorm
  simpa [hv] using this

/-- **Compactness of a unit-shift resolvent of the oscillator closure.** -/
