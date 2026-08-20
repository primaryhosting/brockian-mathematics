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

/-
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Complex
open scoped Convolution

namespace Brockian.Weyl.SchrodingerMinimal

/-! ## Test functions and the minimal Schrödinger expression -/

/-- A test function on the line: smooth with compact support. -/

theorem bounded_ode_solution_eq_zero {c : ℂ} (hc : c.im ≠ 0) {y : ℝ → ℂ} (hy : ContDiff ℝ 2 y)
    (hode : ∀ t, deriv (deriv y) t = c * y t) {M : ℝ} (hbdd : ∀ t, ‖y t‖ ≤ M) :
    ∀ t, y t = 0 := by
  obtain ⟨lam, hlam, hlamre⟩ : ∃ lam : ℂ, lam ^ 2 = c ∧ 0 < lam.re := by
    obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq c (n := 2) (by norm_num)
    have hre : l.re ≠ 0 := by
      intro h; apply hc; rw [← hl]; simp [pow_two, Complex.mul_im, h]
    rcases lt_or_gt_of_ne hre with h | h
    · exact ⟨-l, by rw [neg_pow]; simpa using hl, by simpa using h⟩
    · exact ⟨l, hl, h⟩
  have hlamne : lam ≠ 0 := by intro h; rw [h] at hlamre; simp at hlamre
  have h1 := sol_formula hlam hy hode
  have h2 := sol_formula (c := c) (lam := -lam) (by rw [neg_pow]; simpa using hlam) hy hode
  have hy2 : ∀ t : ℝ, 2 * lam * y t
      = (deriv y 0 + lam * y 0) * Complex.exp (lam * t)
        - (deriv y 0 + -lam * y 0) * Complex.exp (-lam * t) := by
    intro t; linear_combination h1 t - h2 t
  have hnormexp : ∀ t : ℝ, ‖Complex.exp (lam * t)‖ = Real.exp (lam.re * t) := by
    intro t; rw [Complex.norm_exp]; simp [Complex.mul_re]
  have hnormexp' : ∀ t : ℝ, ‖Complex.exp (-lam * t)‖ = Real.exp (-(lam.re * t)) := by
    intro t; rw [Complex.norm_exp]; simp [Complex.mul_re]
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hbdd 0)
  have hn2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  set A := deriv y 0 + lam * y 0 with hAdef
  set B := deriv y 0 + -lam * y 0 with hBdef
  have hA : A = 0 := by
    rw [← norm_eq_zero]
    apply exp_bound_zero hlamre (norm_nonneg A) (C := 2 * ‖lam‖ * M + ‖B‖)
    intro t ht
    have hb1 : ‖A * Complex.exp (lam * t)‖
        ≤ ‖2 * lam * y t‖ + ‖B * Complex.exp (-lam * t)‖ := by
      calc ‖A * Complex.exp (lam * t)‖
          = ‖2 * lam * y t + B * Complex.exp (-lam * t)‖ := by rw [hy2 t]; ring_nf
        _ ≤ _ := norm_add_le _ _
    simp only [norm_mul, hnormexp, hnormexp', hn2] at hb1
    have h4 : Real.exp (-(lam.re * t)) ≤ 1 := by
      apply Real.exp_le_one_iff.2; nlinarith
    nlinarith [norm_nonneg B, norm_nonneg lam, hbdd t, Real.exp_pos (-(lam.re * t))]
  have hB : B = 0 := by
    rw [← norm_eq_zero]
    apply exp_bound_zero' hlamre (norm_nonneg B) (C := 2 * ‖lam‖ * M)
    intro t ht
    have hb1 : ‖B * Complex.exp (-lam * t)‖ ≤ ‖2 * lam * y t‖ := by
      have hz : B * Complex.exp (-lam * t) = -(2 * lam * y t) := by rw [hy2 t, hA]; ring
      rw [hz, norm_neg]
    simp only [norm_mul, hnormexp', hn2] at hb1
    nlinarith [norm_nonneg lam, hbdd t, norm_nonneg (y t)]
  intro t
  have h3 := hy2 t
  rw [hA, hB] at h3
  simp at h3
  rcases h3 with h | h
  · exact absurd h (by simpa using hlamne)
  · exact h

/-! ## Elementary calculus and integration facts -/

