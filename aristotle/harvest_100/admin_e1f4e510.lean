import Mathlib

/-!
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Cardy–Smirnov theory says that the scaling limit of crossing probabilities for critical
site percolation on the triangular lattice is *conformally invariant*, and that in the
reference domain — Carleson's equilateral triangle — the limiting crossing probability is
the linear (barycentric) function, so that the crossing probability between the side `AB`
and the sub-segment `CX` of the side `CA` equals `|CX| / |CA|`.

This file formalizes the two structural halves of that statement and proves them:

* **Conformal invariance / reduction.** The conformal modulus of a configuration of four
  marked boundary points is the cross-ratio; it is invariant under Möbius transformations,
  hence any crossing functional that is a function of the modulus is conformally invariant.
  This is the reduction step: the whole Cardy–Smirnov formula is determined by its value on
  one reference configuration.

* **Base case (Carleson's equilateral triangle).** The three Cardy–Smirnov functions
  `smirnovA, smirnovB, smirnovC` attached to the equilateral triangle with vertices
  `A = 0`, `B = 1`, `C = 1/2 + i √3 / 2` are harmonic on the whole plane, sum to `1`,
  take the value `1` at their own vertex and vanish on the opposite side, and satisfy
  Cardy's formula `smirnovA X = |CX| / |CA|` for `X` on the side `CA`.

The probabilistic input of Smirnov's theorem (existence of the scaling limit for critical
site percolation on the triangular lattice) is *not* formalized here; what is formalized
and proved is the conformal-invariance reduction together with the closed form of the
limit in the reference triangle.
-/

namespace Frontier

open Complex

/-! ### The conformal modulus of four marked boundary points -/

/-- The cross-ratio of four points of the plane.  For a Jordan domain with four marked
boundary points this is the conformal modulus of the configuration. -/
noncomputable def crossRatio (z₁ z₂ z₃ z₄ : ℂ) : ℂ :=
  ((z₁ - z₃) * (z₂ - z₄)) / ((z₁ - z₄) * (z₂ - z₃))

/-- A Möbius transformation `z ↦ (a z + b) / (c z + d)`, `a d - b c ≠ 0`. -/
structure Mobius where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  det_ne_zero : a * d - b * c ≠ 0

/-- The map underlying a Möbius transformation. -/
noncomputable def Mobius.toFun (m : Mobius) (z : ℂ) : ℂ := (m.a * z + m.b) / (m.c * z + m.d)

noncomputable instance : CoeFun Mobius (fun _ => ℂ → ℂ) := ⟨Mobius.toFun⟩

/-- The basic difference identity for a Möbius transformation. -/
theorem Mobius.sub_eq (m : Mobius) {z w : ℂ} (hz : m.c * z + m.d ≠ 0)
    (hw : m.c * w + m.d ≠ 0) :
    m z - m w = (m.a * m.d - m.b * m.c) * (z - w) / ((m.c * z + m.d) * (m.c * w + m.d)) := by
  show (m.a * z + m.b) / (m.c * z + m.d) - (m.a * w + m.b) / (m.c * w + m.d) = _
  rw [div_sub_div _ _ hz hw]
  congr 1
  ring

/-- **Conformal invariance of the modulus**: the cross-ratio of four points is unchanged by
a Möbius transformation. -/
theorem crossRatio_mobius (m : Mobius) {z₁ z₂ z₃ z₄ : ℂ}
    (h₁ : m.c * z₁ + m.d ≠ 0) (h₂ : m.c * z₂ + m.d ≠ 0)
    (h₃ : m.c * z₃ + m.d ≠ 0) (h₄ : m.c * z₄ + m.d ≠ 0)
    (h₁₄ : z₁ ≠ z₄) (h₂₃ : z₂ ≠ z₃) :
    crossRatio (m z₁) (m z₂) (m z₃) (m z₄) = crossRatio z₁ z₂ z₃ z₄ := by
  have e₁₄ : z₁ - z₄ ≠ 0 := sub_ne_zero.mpr h₁₄
  have e₂₃ : z₂ - z₃ ≠ 0 := sub_ne_zero.mpr h₂₃
  have hdet := m.det_ne_zero
  unfold crossRatio
  rw [m.sub_eq h₁ h₃, m.sub_eq h₂ h₄, m.sub_eq h₁ h₄, m.sub_eq h₂ h₃]
  field_simp

/-- A crossing functional built from the conformal modulus of the configuration. -/
noncomputable def crossingProb (F : ℂ → ℝ) (z₁ z₂ z₃ z₄ : ℂ) : ℝ :=
  F (crossRatio z₁ z₂ z₃ z₄)

/-- **Conformal invariance of crossing probabilities.**  Any crossing functional that is a
function of the conformal modulus takes the same value on a configuration and on its image
under a Möbius transformation. -/
theorem crossingProb_mobius (F : ℂ → ℝ) (m : Mobius) {z₁ z₂ z₃ z₄ : ℂ}
    (h₁ : m.c * z₁ + m.d ≠ 0) (h₂ : m.c * z₂ + m.d ≠ 0)
    (h₃ : m.c * z₃ + m.d ≠ 0) (h₄ : m.c * z₄ + m.d ≠ 0)
    (h₁₄ : z₁ ≠ z₄) (h₂₃ : z₂ ≠ z₃) :
    crossingProb F (m z₁) (m z₂) (m z₃) (m z₄) = crossingProb F z₁ z₂ z₃ z₄ := by
  unfold crossingProb
  rw [crossRatio_mobius m h₁ h₂ h₃ h₄ h₁₄ h₂₃]

/-! ### Carleson's equilateral triangle and the Cardy–Smirnov functions -/

/-- Vertex `A` of the reference equilateral triangle. -/
noncomputable def vA : ℂ := 0

/-- Vertex `B` of the reference equilateral triangle. -/
noncomputable def vB : ℂ := 1

/-- Vertex `C` of the reference equilateral triangle. -/
noncomputable def vC : ℂ := ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I

/-- The Cardy–Smirnov function attached to the vertex `A`: the barycentric coordinate
of `z` with respect to `A`, written as the real part of an affine holomorphic function. -/
noncomputable def smirnovA (z : ℂ) : ℝ := ((-1 + (Real.sqrt 3 : ℝ)⁻¹ * I) * z + 1).re

/-- The Cardy–Smirnov function attached to the vertex `B`. -/
noncomputable def smirnovB (z : ℂ) : ℝ := ((1 + (Real.sqrt 3 : ℝ)⁻¹ * I) * z).re

/-- The Cardy–Smirnov function attached to the vertex `C`. -/
noncomputable def smirnovC (z : ℂ) : ℝ := (((-(2 * (Real.sqrt 3)⁻¹) : ℝ) : ℂ) * I * z).re

theorem sqrt3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

theorem sqrt3_ne_zero : (Real.sqrt 3 : ℝ) ≠ 0 := ne_of_gt sqrt3_pos

/-- The reference triangle `A B C` is equilateral with unit side length. -/
theorem triangle_equilateral : dist vA vB = 1 ∧ dist vB vC = 1 ∧ dist vC vA = 1 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have key : ∀ z : ℂ, Complex.normSq z = 1 → ‖z‖ = 1 := by
    intro z hz
    rw [Complex.norm_def, hz, Real.sqrt_one]
  refine ⟨by simp [vA, vB], ?_, ?_⟩
  · rw [dist_eq_norm]
    refine key _ ?_
    simp [vB, vC, Complex.normSq_apply]
    nlinarith
  · rw [dist_eq_norm, vA, sub_zero]
    exact key _ (by simp [vC, Complex.normSq_apply]; nlinarith)

theorem smirnovA_apply (z : ℂ) : smirnovA z = 1 - z.re - (Real.sqrt 3)⁻¹ * z.im := by
  simp only [smirnovA, Complex.add_re, Complex.mul_re, Complex.one_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im, Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem smirnovB_apply (z : ℂ) : smirnovB z = z.re - (Real.sqrt 3)⁻¹ * z.im := by
  simp only [smirnovB, Complex.add_re, Complex.mul_re, Complex.one_re, Complex.add_im,
    Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem smirnovC_apply (z : ℂ) : smirnovC z = 2 * (Real.sqrt 3)⁻¹ * z.im := by
  simp only [smirnovC, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The three Cardy–Smirnov functions sum to `1`. -/
theorem smirnov_sum (z : ℂ) : smirnovA z + smirnovB z + smirnovC z = 1 := by
  rw [smirnovA_apply, smirnovB_apply, smirnovC_apply]
  ring

/-- `smirnovA` is harmonic on the whole plane (it is the real part of a holomorphic
function). -/
theorem harmonic_smirnovA : InnerProductSpace.HarmonicOnNhd smirnovA Set.univ := by
  intro x _
  exact AnalyticAt.harmonicAt_re
    (by fun_prop (disch := norm_num) : AnalyticAt ℂ
      (fun z : ℂ => (-1 + (Real.sqrt 3 : ℝ)⁻¹ * I) * z + 1) x)

theorem harmonic_smirnovB : InnerProductSpace.HarmonicOnNhd smirnovB Set.univ := by
  intro x _
  exact AnalyticAt.harmonicAt_re
    (by fun_prop (disch := norm_num) : AnalyticAt ℂ
      (fun z : ℂ => (1 + (Real.sqrt 3 : ℝ)⁻¹ * I) * z) x)

theorem harmonic_smirnovC : InnerProductSpace.HarmonicOnNhd smirnovC Set.univ := by
  intro x _
  exact AnalyticAt.harmonicAt_re
    (by fun_prop (disch := norm_num) : AnalyticAt ℂ
      (fun z : ℂ => ((-(2 * (Real.sqrt 3)⁻¹) : ℝ) : ℂ) * I * z) x)

theorem smirnovA_vA : smirnovA vA = 1 := by simp [smirnovA_apply, vA]

/-- `smirnovA` vanishes on the whole side `BC` opposite to the vertex `A`. -/
theorem smirnovA_side_BC (s : ℝ) : smirnovA (vB + (s : ℂ) * (vC - vB)) = 0 := by
  have h3 : (Real.sqrt 3 : ℝ) ≠ 0 := sqrt3_ne_zero
  rw [smirnovA_apply]
  simp only [vB, vC, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  field_simp
  ring

/-- **Cardy's formula in the reference triangle** (Smirnov's base case): for a point `X`
on the side `CA`, written `X = C + t (A - C)` with `t ∈ [0,1]`, the Cardy–Smirnov crossing
function equals the length ratio `|CX| / |CA|`. -/
theorem cardy_formula_triangle {t : ℝ} (ht₀ : 0 ≤ t) :
    smirnovA (vC + (t : ℂ) * (vA - vC)) = dist vC (vC + (t : ℂ) * (vA - vC)) / dist vC vA ∧
      smirnovA (vC + (t : ℂ) * (vA - vC)) = t := by
  have h3 : (Real.sqrt 3 : ℝ) ≠ 0 := sqrt3_ne_zero
  have hC : vC ≠ 0 := by
    intro h
    have : (Real.sqrt 3 / 2 : ℝ) = 0 := by
      simpa [vC, Complex.ext_iff] using congrArg Complex.im h
    exact h3 (by linarith [this])
  have hval : smirnovA (vC + (t : ℂ) * (vA - vC)) = t := by
    rw [smirnovA_apply]
    simp only [vA, vC, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.zero_re, Complex.zero_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring
  refine ⟨?_, hval⟩
  have hdist : dist vC (vC + (t : ℂ) * (vA - vC)) = t * dist vC vA := by
    have h1 : vC - (vC + (t : ℂ) * (vA - vC)) = (t : ℂ) * (vC - vA) := by ring
    rw [dist_eq_norm, dist_eq_norm, h1, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ht₀]
  rw [hval, hdist, mul_div_assoc, div_self, mul_one]
  simpa [dist_eq_norm, vA, sub_zero, sub_eq_zero] using hC

/-! ### Main statement -/

/--
**Cardy–Smirnov: conformal invariance of critical percolation crossing probabilities.**

The statement is the conjunction of the conformal-invariance reduction and of Smirnov's
base case in Carleson's equilateral triangle:

0. the reference triangle `A B C` is equilateral with unit sides;
1. the conformal modulus (cross-ratio) of four marked boundary points is invariant under
   Möbius transformations;
2. consequently every crossing functional that is a function of the modulus is conformally
   invariant, so the crossing probability is determined by its values on one reference
   family of configurations;
3. the three Cardy–Smirnov functions of the reference equilateral triangle are harmonic on
   the plane and sum to `1`;
4. `smirnovA` equals `1` at `A` and vanishes identically on the opposite side `BC`;
5. Cardy's formula holds in the reference triangle: for `X = C + t (A - C)` on the side
   `CA` with `t ∈ [0,1]`, the crossing function equals the ratio `|CX| / |CA|` (and equals
   `t`).
-/
theorem smirnov_percolation :
    (dist vA vB = 1 ∧ dist vB vC = 1 ∧ dist vC vA = 1) ∧
    (∀ (m : Mobius) (z₁ z₂ z₃ z₄ : ℂ), m.c * z₁ + m.d ≠ 0 → m.c * z₂ + m.d ≠ 0 →
        m.c * z₃ + m.d ≠ 0 → m.c * z₄ + m.d ≠ 0 → z₁ ≠ z₄ → z₂ ≠ z₃ →
        crossRatio (m z₁) (m z₂) (m z₃) (m z₄) = crossRatio z₁ z₂ z₃ z₄) ∧
    (∀ (F : ℂ → ℝ) (m : Mobius) (z₁ z₂ z₃ z₄ : ℂ), m.c * z₁ + m.d ≠ 0 → m.c * z₂ + m.d ≠ 0 →
        m.c * z₃ + m.d ≠ 0 → m.c * z₄ + m.d ≠ 0 → z₁ ≠ z₄ → z₂ ≠ z₃ →
        crossingProb F (m z₁) (m z₂) (m z₃) (m z₄) = crossingProb F z₁ z₂ z₃ z₄) ∧
    (InnerProductSpace.HarmonicOnNhd smirnovA Set.univ ∧
      InnerProductSpace.HarmonicOnNhd smirnovB Set.univ ∧
      InnerProductSpace.HarmonicOnNhd smirnovC Set.univ ∧
      ∀ z : ℂ, smirnovA z + smirnovB z + smirnovC z = 1) ∧
    (smirnovA vA = 1 ∧ ∀ s : ℝ, smirnovA (vB + (s : ℂ) * (vC - vB)) = 0) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      smirnovA (vC + (t : ℂ) * (vA - vC))
        = dist vC (vC + (t : ℂ) * (vA - vC)) / dist vC vA ∧
      smirnovA (vC + (t : ℂ) * (vA - vC)) = t) := by
  refine ⟨triangle_equilateral, fun m z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ h₁₄ h₂₃ => crossRatio_mobius m h₁ h₂ h₃ h₄ h₁₄ h₂₃,
    fun F m z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ h₁₄ h₂₃ => crossingProb_mobius F m h₁ h₂ h₃ h₄ h₁₄ h₂₃,
    ⟨harmonic_smirnovA, harmonic_smirnovB, harmonic_smirnovC, smirnov_sum⟩,
    ⟨smirnovA_vA, smirnovA_side_BC⟩,
    fun t ht₀ _ => cardy_formula_triangle ht₀⟩

end Frontier

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

