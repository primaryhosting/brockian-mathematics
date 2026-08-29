/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter MeasureTheory Topology Complex

namespace Phys

/-- `‖z‖ ^ 2` in terms of the real and imaginary parts of `z`. -/
private lemma sq_norm_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring

/-- Real part of a differentiable `ℂ`-valued function of a real variable. -/
private lemma hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).re) f'.re x :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h

/-- Imaginary part of a differentiable `ℂ`-valued function of a real variable. -/
private lemma hasDerivAt_im {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).im) f'.im x :=
  Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h

/--
**Quantum virial theorem** (one dimension, units `ħ = 2m = 1`).

Let `ψ` be a stationary state of energy `E` for the Hamiltonian `-d²/dx² + V`, i.e.
`-ψ'' + V ψ = E ψ`, where `dψ`, `ddψ` are the first and second derivatives of `ψ` and `dV` is
the derivative of `V`.  Assume the state is *bound*: the kinetic density `‖ψ'‖²`, the potential
density `(V - E)‖ψ‖²` and the virial density `x V'(x) ‖ψ‖²` are integrable, and the boundary
terms `‖ψ‖ ‖ψ'‖` and `x (‖ψ'‖² - (V - E)‖ψ‖²)` vanish at `±∞`.

Then twice the expected kinetic energy equals the expectation of the virial `x ∂ₓV`:
`2 ⟨T⟩ = ⟨x · ∇V⟩`.
-/
theorem virial_theorem (ψ dψ ddψ : ℝ → ℂ) (V dV : ℝ → ℝ) (E : ℝ)
    (hψ : ∀ x, HasDerivAt ψ (dψ x) x)
    (hdψ : ∀ x, HasDerivAt dψ (ddψ x) x)
    (hV : ∀ x, HasDerivAt V (dV x) x)
    (hSchr : ∀ x, -ddψ x + (V x : ℂ) * ψ x = (E : ℂ) * ψ x)
    (hT : Integrable fun x => ‖dψ x‖ ^ 2)
    (hU : Integrable fun x => (V x - E) * ‖ψ x‖ ^ 2)
    (hW : Integrable fun x => x * dV x * ‖ψ x‖ ^ 2)
    (hbot1 : Tendsto (fun x => ‖ψ x‖ * ‖dψ x‖) atBot (𝓝 0))
    (htop1 : Tendsto (fun x => ‖ψ x‖ * ‖dψ x‖) atTop (𝓝 0))
    (hbot2 : Tendsto (fun x => x * (‖dψ x‖ ^ 2 - (V x - E) * ‖ψ x‖ ^ 2)) atBot (𝓝 0))
    (htop2 : Tendsto (fun x => x * (‖dψ x‖ ^ 2 - (V x - E) * ‖ψ x‖ ^ 2)) atTop (𝓝 0)) :
    2 * ∫ x, ‖dψ x‖ ^ 2 = ∫ x, x * dV x * ‖ψ x‖ ^ 2 := by
  -- Componentwise derivatives
  have hA : ∀ x, HasDerivAt (fun y => (ψ y).re) ((dψ x).re) x := fun x => hasDerivAt_re (hψ x)
  have hB : ∀ x, HasDerivAt (fun y => (ψ y).im) ((dψ x).im) x := fun x => hasDerivAt_im (hψ x)
  have hA' : ∀ x, HasDerivAt (fun y => (dψ y).re) ((ddψ x).re) x := fun x => hasDerivAt_re (hdψ x)
  have hB' : ∀ x, HasDerivAt (fun y => (dψ y).im) ((ddψ x).im) x := fun x => hasDerivAt_im (hdψ x)
  -- The stationary Schrödinger equation, in components
  have hdd : ∀ x, ddψ x = ((V x - E : ℝ) : ℂ) * ψ x := by
    intro x; have h := hSchr x; push_cast; linear_combination -h
  have hddre : ∀ x, (ddψ x).re = (V x - E) * (ψ x).re := by
    intro x; rw [hdd x]; simp
  have hddim : ∀ x, (ddψ x).im = (V x - E) * (ψ x).im := by
    intro x; rw [hdd x]; simp
  -- First integration by parts: `∫ (‖ψ'‖² + (V - E)‖ψ‖²) = 0`
  have hgderiv : ∀ x, HasDerivAt (fun y => (ψ y).re * (dψ y).re + (ψ y).im * (dψ y).im)
      (‖dψ x‖ ^ 2 + (V x - E) * ‖ψ x‖ ^ 2) x := by
    intro x
    have h := ((hA x).mul (hA' x)).add ((hB x).mul (hB' x))
    convert h using 1
    rw [sq_norm_eq, sq_norm_eq, hddre x, hddim x]; ring
  have hbound : ∀ x, ‖(ψ x).re * (dψ x).re + (ψ x).im * (dψ x).im‖ ≤ ‖ψ x‖ * ‖dψ x‖ := by
    intro x
    have hre : (ψ x).re * (dψ x).re + (ψ x).im * (dψ x).im
        = ((starRingEnd ℂ) (ψ x) * dψ x).re := by
      simp [Complex.mul_re]
    rw [hre]
    calc ‖((starRingEnd ℂ) (ψ x) * dψ x).re‖ ≤ ‖(starRingEnd ℂ) (ψ x) * dψ x‖ :=
          Complex.abs_re_le_norm _
      _ = ‖ψ x‖ * ‖dψ x‖ := by rw [norm_mul, RCLike.norm_conj]
  have key1 : ∫ x, (‖dψ x‖ ^ 2 + (V x - E) * ‖ψ x‖ ^ 2) = 0 := by
    simpa using integral_of_hasDerivAt_of_tendsto hgderiv (hT.add hU)
      (squeeze_zero_norm hbound hbot1) (squeeze_zero_norm hbound htop1)
  -- Second integration by parts: `∫ (‖ψ'‖² - (V - E)‖ψ‖² - x V' ‖ψ‖²) = 0`
  have hFderiv : ∀ x, HasDerivAt (fun y => y * (‖dψ y‖ ^ 2 - (V y - E) * ‖ψ y‖ ^ 2))
      (‖dψ x‖ ^ 2 - (V x - E) * ‖ψ x‖ ^ 2 - x * dV x * ‖ψ x‖ ^ 2) x := by
    intro x
    simp only [sq_norm_eq]
    have hQ := ((hA' x).pow 2).add ((hB' x).pow 2)
    have hP := ((hA x).pow 2).add ((hB x).pow 2)
    have hVE : HasDerivAt (fun y => V y - E) (dV x) x := (hV x).sub_const E
    have h := (hasDerivAt_id x).mul (hQ.sub (hVE.mul hP))
    convert h using 1
    simp only [id_eq, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    rw [hddre x, hddim x]; ring
  have key2 : ∫ x, (‖dψ x‖ ^ 2 - (V x - E) * ‖ψ x‖ ^ 2 - x * dV x * ‖ψ x‖ ^ 2) = 0 := by
    simpa using integral_of_hasDerivAt_of_tendsto hFderiv ((hT.sub hU).sub hW) hbot2 htop2
  have e1 := integral_sub (hT.sub hU) hW
  have e2 := integral_sub hT hU
  simp only [Pi.sub_apply] at e1 e2
  rw [integral_add hT hU] at key1
  rw [e1, e2] at key2
  linarith

/-!
## Non-vacuity: the harmonic oscillator ground state

The hypotheses of `Phys.virial_theorem` are simultaneously satisfiable: they hold for the ground
state `ψ(x) = exp (-x²/2)` of the harmonic oscillator `V(x) = x²` (energy `E = 1`).
-/

namespace HarmonicOscillator

/-- Ground state of the harmonic oscillator (units `ħ = 2m = 1`). -/
noncomputable def psi (x : ℝ) : ℂ := (Real.exp (-x ^ 2 / 2) : ℝ)

/-- Derivative of the ground state. -/
noncomputable def dpsi (x : ℝ) : ℂ := ((-x) * Real.exp (-x ^ 2 / 2) : ℝ)

/-- Second derivative of the ground state. -/
noncomputable def ddpsi (x : ℝ) : ℂ := ((x ^ 2 - 1) * Real.exp (-x ^ 2 / 2) : ℝ)

/-- The harmonic potential. -/
def pot (x : ℝ) : ℝ := x ^ 2

/-- Derivative of the harmonic potential. -/
def dpot (x : ℝ) : ℝ := 2 * x

private lemma exp_half_sq (x : ℝ) :
    Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) = Real.exp (-x ^ 2) := by
  rw [← Real.exp_add]; ring_nf

lemma norm_psi_sq (x : ℝ) : ‖psi x‖ ^ 2 = Real.exp (-x ^ 2) := by
  rw [psi, Complex.norm_real, Real.norm_eq_abs, sq_abs, sq, exp_half_sq]

lemma norm_dpsi_sq (x : ℝ) : ‖dpsi x‖ ^ 2 = x ^ 2 * Real.exp (-x ^ 2) := by
  rw [dpsi, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [mul_pow, sq (Real.exp _), exp_half_sq]
  ring

private lemma integrable_gauss : Integrable fun x : ℝ => Real.exp (-x ^ 2) := by
  simpa using integrable_exp_neg_mul_sq (b := 1) one_pos

private lemma integrable_sq_gauss : Integrable fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2)) volume := by
    fun_prop
  have hg : Integrable fun x : ℝ => 2 * Real.exp (-(1 / 2) * x ^ 2) :=
    (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul 2
  refine Integrable.mono' hg hmeas (Filter.Eventually.of_forall fun x => ?_)
  have hx : x ^ 2 / 2 ≤ Real.exp (x ^ 2 / 2) := (Real.add_one_le_exp _).trans' (by linarith)
  have hpos : (0:ℝ) < Real.exp (-x ^ 2) := Real.exp_pos _
  have hsplit : Real.exp (-x ^ 2) = Real.exp (-(1 / 2) * x ^ 2) * Real.exp (-(x ^ 2 / 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hsplit]
  have hinv : Real.exp (-(x ^ 2 / 2)) * Real.exp (x ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h2 : x ^ 2 * Real.exp (-(x ^ 2 / 2)) ≤ 2 := by
    nlinarith [Real.exp_pos (-(x ^ 2 / 2)), Real.exp_pos (x ^ 2 / 2)]
  calc x ^ 2 * (Real.exp (-(1 / 2) * x ^ 2) * Real.exp (-(x ^ 2 / 2)))
      = (x ^ 2 * Real.exp (-(x ^ 2 / 2))) * Real.exp (-(1 / 2) * x ^ 2) := by ring
    _ ≤ 2 * Real.exp (-(1 / 2) * x ^ 2) := by
        exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le

private lemma tendsto_abs_gauss_cocompact :
    Tendsto (fun x : ℝ => |x| * Real.exp (-x ^ 2)) (cocompact ℝ) (𝓝 0) := by
  have h := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a := 1) one_pos 1
  simpa using h

private lemma tendsto_abs_gauss_atBot :
    Tendsto (fun x : ℝ => |x| * Real.exp (-x ^ 2)) atBot (𝓝 0) := by
  have h := tendsto_abs_gauss_cocompact
  rw [cocompact_eq_atBot_atTop] at h
  exact h.mono_left le_sup_left

private lemma tendsto_abs_gauss_atTop :
    Tendsto (fun x : ℝ => |x| * Real.exp (-x ^ 2)) atTop (𝓝 0) := by
  have h := tendsto_abs_gauss_cocompact
  rw [cocompact_eq_atBot_atTop] at h
  exact h.mono_left le_sup_right

/-- The hypotheses of the virial theorem are satisfiable: the harmonic oscillator ground state
is a genuine bound stationary state, and for it the virial theorem indeed holds. -/
theorem virial_theorem_harmonic_oscillator :
    2 * ∫ x : ℝ, ‖dpsi x‖ ^ 2 = ∫ x : ℝ, x * dpot x * ‖psi x‖ ^ 2 := by
  have hnorms : ∀ x : ℝ, ‖psi x‖ ^ 2 = Real.exp (-x ^ 2) := norm_psi_sq
  have hnormd : ∀ x : ℝ, ‖dpsi x‖ ^ 2 = x ^ 2 * Real.exp (-x ^ 2) := norm_dpsi_sq
  have hexp : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2 / 2))
      ((-x) * Real.exp (-x ^ 2 / 2)) x := by
    intro x
    have h : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
      have := (hasDerivAt_pow 2 x).neg.div_const 2
      convert this using 1
      ring
    simpa [mul_comm] using h.exp
  refine Phys.virial_theorem psi dpsi ddpsi pot dpot 1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x
    exact (hexp x).ofReal_comp
  · intro x
    have h : HasDerivAt (fun y : ℝ => (-y) * Real.exp (-y ^ 2 / 2))
        ((x ^ 2 - 1) * Real.exp (-x ^ 2 / 2)) x := by
      have h1 : HasDerivAt (fun y : ℝ => -y) (-1 : ℝ) x := by
        simpa using (hasDerivAt_id x).neg
      have h2 := h1.mul (hexp x)
      convert h2 using 1
      ring
    exact h.ofReal_comp
  · intro x
    simpa [pot, dpot] using (hasDerivAt_pow 2 x)
  · intro x
    simp only [psi, ddpsi, pot]
    push_cast
    ring
  · exact integrable_sq_gauss.congr (by filter_upwards with x using (hnormd x).symm)
  · refine (integrable_sq_gauss.sub integrable_gauss).congr ?_
    filter_upwards with x
    simp only [Pi.sub_apply]
    rw [hnorms x, pot]
    ring
  · refine (integrable_sq_gauss.const_mul 2).congr ?_
    filter_upwards with x
    rw [hnorms x, dpot]
    ring
  · refine (tendsto_abs_gauss_atBot).congr fun x => ?_
    rw [psi, dpsi, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le, abs_mul, abs_neg, abs_of_nonneg (Real.exp_pos _).le]
    rw [← mul_assoc, mul_comm (Real.exp (-x ^ 2 / 2)) |x|, mul_assoc, exp_half_sq]
  · refine (tendsto_abs_gauss_atTop).congr fun x => ?_
    rw [psi, dpsi, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le, abs_mul, abs_neg, abs_of_nonneg (Real.exp_pos _).le]
    rw [← mul_assoc, mul_comm (Real.exp (-x ^ 2 / 2)) |x|, mul_assoc, exp_half_sq]
  · refine squeeze_zero_norm (fun x => ?_) tendsto_abs_gauss_atBot
    rw [hnorms x, hnormd x, pot, Real.norm_eq_abs, abs_mul]
    have : x ^ 2 * Real.exp (-x ^ 2) - (x ^ 2 - 1) * Real.exp (-x ^ 2) = Real.exp (-x ^ 2) := by
      ring
    rw [this, abs_of_nonneg (Real.exp_pos _).le]
  · refine squeeze_zero_norm (fun x => ?_) tendsto_abs_gauss_atTop
    rw [hnorms x, hnormd x, pot, Real.norm_eq_abs, abs_mul]
    have : x ^ 2 * Real.exp (-x ^ 2) - (x ^ 2 - 1) * Real.exp (-x ^ 2) = Real.exp (-x ^ 2) := by
      ring
    rw [this, abs_of_nonneg (Real.exp_pos _).le]

end HarmonicOscillator

end Phys

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

