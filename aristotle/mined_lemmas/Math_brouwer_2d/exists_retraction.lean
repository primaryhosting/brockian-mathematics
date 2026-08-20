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

namespace BrouwerAux

/-- The radial retraction of the plane `ℂ` onto the closed unit disk. -/

theorem exists_retraction (g : ℂ → ℂ) (hg : Continuous g) (hgb : ∀ z, ‖g z‖ ≤ 1)
    (hne : ∀ z, g z ≠ proj z) :
    ∃ R : ℂ → ℂ, Continuous R ∧ (∀ z, ‖R z‖ = 1) ∧ (∀ z, ‖z‖ = 1 → R z = z) := by
  set w : ℂ → ℂ := proj with hwdef
  set v : ℂ → ℂ := fun z => w z - g z with hvdef
  have hvpos : ∀ z, 0 < ‖v z‖ := fun z => norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm (hne z)))
  set B : ℂ → ℝ := fun z => (w z).re * (v z).re + (w z).im * (v z).im with hBdef
  set A : ℂ → ℝ := fun z => ‖v z‖ ^ 2 with hAdef
  have hA : ∀ z, 0 < A z := fun z => pow_pos (hvpos z) 2
  set C : ℂ → ℝ := fun z => 1 - ‖w z‖ ^ 2 with hCdef
  have hC : ∀ z, 0 ≤ C z := by
    intro z
    have h1 := norm_proj_le z
    have h2 := norm_nonneg (w z)
    simp only [hCdef]
    nlinarith
  set S : ℂ → ℝ := fun z => Real.sqrt (B z ^ 2 + A z * C z) with hSdef
  have hS2 : ∀ z, S z ^ 2 = B z ^ 2 + A z * C z := by
    intro z
    apply Real.sq_sqrt
    nlinarith [sq_nonneg (B z), (hA z).le, hC z]
  set T : ℂ → ℝ := fun z => (-B z + S z) / A z with hTdef
  have hkey : ∀ z, ‖w z + (T z : ℂ) * v z‖ ^ 2 = 1 := by
    intro z
    rw [norm_add_smul_sq]
    have h := quad_root (A z) (B z) (C z) (S z) (T z) (hA z).ne' (hS2 z) rfl
    simp only [hAdef] at h ⊢
    simp only [hCdef] at *
    linarith [h]
  have hwc : Continuous w := continuous_proj
  have hvc : Continuous v := hwc.sub hg
  have hBc : Continuous B :=
    ((Complex.continuous_re.comp hwc).mul (Complex.continuous_re.comp hvc)).add
      ((Complex.continuous_im.comp hwc).mul (Complex.continuous_im.comp hvc))
  have hAc : Continuous A := hvc.norm.pow 2
  have hCc : Continuous C := continuous_const.sub (hwc.norm.pow 2)
  have hSc : Continuous S := Real.continuous_sqrt.comp ((hBc.pow 2).add (hAc.mul hCc))
  have hTc : Continuous T := (hBc.neg.add hSc).div hAc (fun z => (hA z).ne')
  refine ⟨fun z => w z + (T z : ℂ) * v z, hwc.add ((Complex.continuous_ofReal.comp hTc).mul hvc),
    ?_, ?_⟩
  · intro z
    nlinarith [norm_nonneg (w z + (T z : ℂ) * v z), hkey z]
  · intro z hz
    have hwz : w z = z := proj_eq_self hz.le
    have hCz : C z = 0 := by simp [hCdef, hwz, hz]
    have hBz : 0 ≤ B z := by
      have hgz : ‖g z‖ ^ 2 ≤ 1 := by nlinarith [hgb z, norm_nonneg (g z)]
      rw [sqnorm] at hgz
      have hz2 : z.re ^ 2 + z.im ^ 2 = 1 := by rw [← sqnorm, hz]; norm_num
      simp only [hBdef, hvdef, hwz, Complex.sub_re, Complex.sub_im]
      nlinarith [sq_nonneg (z.re * (g z).im - z.im * (g z).re),
        sq_nonneg (z.re * (g z).re + z.im * (g z).im - 1)]
    have hSz : S z = B z := by
      simp only [hSdef, hCz, mul_zero, add_zero]
      rw [Real.sqrt_sq hBz]
    have hTz : T z = 0 := by simp [hTdef, hSz]
    simp [hTz, hwz]

/-- Brouwer's fixed point theorem for the closed unit disk in `ℂ`. -/
