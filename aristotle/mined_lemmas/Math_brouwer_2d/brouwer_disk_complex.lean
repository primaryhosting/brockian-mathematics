/-
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open Complex Metric Set

/-- On a simply connected, locally path connected space, every continuous nowhere-vanishing
complex-valued function has a continuous logarithm.  This is the lifting property of the
covering map `exp : ℂ → ℂ \ {0}`. -/

theorem brouwer_disk_complex (f : ℂ → ℂ) (hf : ContinuousOn f (closedBall 0 1))
    (hmaps : MapsTo f (closedBall (0 : ℂ) 1) (closedBall 0 1)) :
    ∃ z ∈ closedBall (0 : ℂ) 1, f z = z := by
  by_contra hcon
  push_neg at hcon
  haveI : SimplyConnectedSpace (ℝ × ℝ) := SimplyConnectedSpace.ofContractible (ℝ × ℝ)
  -- `q` parametrises the disk by radius (clamped to `[0,1]`) and angle.
  set q : ℝ × ℝ → ℂ := fun p => ((max 0 (min 1 p.1) : ℝ) : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)
    with hq
  have hq_cont : Continuous q := by
    have h1 : Continuous fun p : ℝ × ℝ => (max 0 (min 1 p.1) : ℝ) :=
      continuous_const.max (continuous_const.min continuous_fst)
    exact (Complex.continuous_ofReal.comp h1).mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hq_mem : ∀ p, q p ∈ closedBall (0 : ℂ) 1 := by
    intro p
    have h1 : ‖Complex.exp ((p.2 : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I p.2
    have h2 : (0 : ℝ) ≤ max 0 (min 1 p.1) := le_max_left _ _
    have h3 : max 0 (min 1 p.1) ≤ 1 := max_le zero_le_one (min_le_left _ _)
    simp only [hq, mem_closedBall, dist_zero_right, norm_mul, h1, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg h2]
    exact h3
  -- the nowhere-vanishing displacement field
  set Φ : ℝ × ℝ → ℂ := fun p => q p - f (q p) with hΦ
  have hΦ_cont : Continuous Φ := hq_cont.sub (hf.comp_continuous hq_cont hq_mem)
  have hΦ_ne : ∀ p, Φ p ≠ 0 := fun p h =>
    hcon (q p) (hq_mem p) (sub_eq_zero.mp h).symm
  obtain ⟨L, hL_cont, hL⟩ := exists_continuous_clog Φ hΦ_cont hΦ_ne
  set E : ℂ → {z : ℂ // z ≠ 0} := fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩ with hE
  have hcov : IsCoveringMap E := Complex.isCoveringMap_exp
  -- Step A: the lift is constant on the degenerate circle of radius `0`.
  have hA : ∀ θ θ' : ℝ, L (0, θ) = L (0, θ') := by
    refine hcov.const_of_comp (g := fun θ : ℝ => L (0, θ))
      (hL_cont.comp (Continuous.prodMk continuous_const continuous_id)) ?_
    intro a a'
    refine Subtype.ext ?_
    show Complex.exp (L (0, a)) = Complex.exp (L (0, a'))
    have e1 : q (0, a) = 0 := by simp [hq]
    have e2 : q (0, a') = 0 := by simp [hq]
    rw [hL, hL, hΦ]
    simp [e1, e2]
  -- Step B: the "winding increment" is independent of the radius, hence zero.
  have hqper : ∀ s : ℝ, q (s, 2 * Real.pi) = q (s, 0) := by
    intro s
    simp [hq, Complex.exp_two_pi_mul_I]
  have hΦper : ∀ s : ℝ, Φ (s, 2 * Real.pi) = Φ (s, 0) := by
    intro s; simp only [hΦ, hqper s]
  have hB : ∀ s : ℝ, L (s, 2 * Real.pi) - L (s, 0) = L (0, 2 * Real.pi) - L (0, 0) := by
    intro s
    refine hcov.const_of_comp (g := fun s : ℝ => L (s, 2 * Real.pi) - L (s, 0)) ?_ ?_ s 0
    · exact (hL_cont.comp (Continuous.prodMk continuous_id continuous_const)).sub
        (hL_cont.comp (Continuous.prodMk continuous_id continuous_const))
    · intro a a'
      refine Subtype.ext ?_
      show Complex.exp (L (a, 2 * Real.pi) - L (a, 0)) = Complex.exp (L (a', 2 * Real.pi) - L (a', 0))
      rw [Complex.exp_sub, Complex.exp_sub, hL, hL, hL, hL, hΦper a, hΦper a',
        div_self (hΦ_ne (a, 0)), div_self (hΦ_ne (a', 0))]
  have hB1 : L (1, 2 * Real.pi) - L (1, 0) = 0 := by
    rw [hB 1, hA (2 * Real.pi) 0, sub_self]
  -- Step C: on the boundary circle, the displacement has a continuous logarithm.
  have hcirc : ∀ θ : ℝ, Complex.exp ((θ : ℂ) * Complex.I) ∈ closedBall (0 : ℂ) 1 := by
    intro θ
    simp [mem_closedBall, Complex.norm_exp_ofReal_mul_I]
  set w : ℝ → ℂ := fun θ =>
    1 - Complex.exp (-(θ : ℂ) * Complex.I) * f (Complex.exp ((θ : ℂ) * Complex.I)) with hw
  have hq1 : ∀ θ : ℝ, q (1, θ) = Complex.exp ((θ : ℂ) * Complex.I) := by
    intro θ; simp [hq]
  have hinv : ∀ θ : ℝ,
      Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-(θ : ℂ) * Complex.I) = 1 := by
    intro θ; rw [← Complex.exp_add]; ring_nf; simp
  have hΦ1 : ∀ θ : ℝ, Φ (1, θ) = Complex.exp ((θ : ℂ) * Complex.I) * w θ := by
    intro θ
    simp only [hΦ, hq1, hw]
    rw [mul_sub, mul_one, ← mul_assoc, hinv θ, one_mul]
  have hw_ne : ∀ θ : ℝ, w θ ≠ 0 := by
    intro θ h
    exact hΦ_ne (1, θ) (by rw [hΦ1 θ, h, mul_zero])
  have hw_re : ∀ θ : ℝ, 0 ≤ (w θ).re := by
    intro θ
    have hnorm : ‖Complex.exp (-(θ : ℂ) * Complex.I)‖ = 1 := by
      have : -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have hfle : ‖f (Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ 1 := by
      have := hmaps (hcirc θ)
      simpa [mem_closedBall, dist_zero_right] using this
    have hre : (Complex.exp (-(θ : ℂ) * Complex.I) *
        f (Complex.exp ((θ : ℂ) * Complex.I))).re ≤ 1 := by
      refine le_trans (Complex.re_le_norm _) ?_
      rw [norm_mul, hnorm, one_mul]
      exact hfle
    simp only [hw, Complex.sub_re, Complex.one_re]
    linarith
  have hw_cont : Continuous w := by
    have h1 : Continuous fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I) :=
      Complex.continuous_exp.comp ((Complex.continuous_ofReal).mul continuous_const)
    have h2 : Continuous fun θ : ℝ => Complex.exp (-(θ : ℂ) * Complex.I) :=
      Complex.continuous_exp.comp (((Complex.continuous_ofReal).neg).mul continuous_const)
    exact continuous_const.sub (h2.mul (hf.comp_continuous h1 hcirc))
  have hw_slit : ∀ θ : ℝ, w θ ∈ Complex.slitPlane := fun θ =>
    mem_slitPlane_of_re_nonneg (hw_re θ) (hw_ne θ)
  have hlog_cont : Continuous fun θ : ℝ => Complex.log (w θ) := hw_cont.clog hw_slit
  -- Step D: compare the two lifts of the boundary displacement.
  set c : ℂ := L (1, 0) - Complex.log (w 0) with hc
  have hexpc : Complex.exp c = 1 := by
    rw [hc, Complex.exp_sub, hL, hΦ1 0, Complex.exp_log (hw_ne 0)]
    have h0 : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by simp
    rw [h0, one_mul, div_self (hw_ne 0)]
  have hlifts : (fun θ : ℝ => L (1, θ))
      = fun θ : ℝ => (θ : ℂ) * Complex.I + Complex.log (w θ) + c := by
    refine hcov.eq_of_comp_eq (hL_cont.comp (Continuous.prodMk continuous_const continuous_id))
      (((Complex.continuous_ofReal.mul continuous_const).add hlog_cont).add continuous_const)
      ?_ 0 ?_
    · funext θ
      refine Subtype.ext ?_
      show Complex.exp (L (1, θ))
        = Complex.exp ((θ : ℂ) * Complex.I + Complex.log (w θ) + c)
      rw [hL, hΦ1 θ, Complex.exp_add, Complex.exp_add, Complex.exp_log (hw_ne θ), hexpc, mul_one]
    · show L (1, 0) = ((0 : ℝ) : ℂ) * Complex.I + Complex.log (w 0) + c
      rw [hc]; push_cast; ring
  have hwper : w (2 * Real.pi) = w 0 := by
    have e3 : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
      rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
    simp [hw, e3, Complex.exp_two_pi_mul_I]
  have key := congrFun hlifts (2 * Real.pi)
  have key0 := congrFun hlifts 0
  have h1 : L (1, 2 * Real.pi) - L (1, 0) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
    rw [key, key0, hwper]
    push_cast
    ring
  rw [hB1] at h1
  simpa [Real.pi_ne_zero] using congrArg Complex.im h1.symm

/-- **Brouwer's fixed point theorem in dimension two**: every continuous self-map of the
closed 2-disk has a fixed point. -/
