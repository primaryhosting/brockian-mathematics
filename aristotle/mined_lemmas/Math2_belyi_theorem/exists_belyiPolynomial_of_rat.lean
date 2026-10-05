import RequestProject.BelyiPoly

/-!
# Belyi polynomials for finite sets of rational points

A polynomial `f ∈ ℚ[X]` is *Belyi* if it is non-constant and all of its finite critical values
(computed over `ℂ`) lie in `{0, 1}`; viewed as a map `ℙ¹ → ℙ¹` such an `f` is ramified only
above `{0, 1, ∞}`.

The main result of this file is `Math2.exists_belyiPolynomial_of_rat`: for every finite set of
rational numbers there is a Belyi polynomial taking each of them to `0` or `1`.
-/

set_option maxRecDepth 8000

namespace Math2

open Polynomial

/-- `f` is a Belyi polynomial: non-constant, with all finite critical values in `{0, 1}`. -/

theorem exists_belyiPolynomial_of_rat (S : Finset ℚ) :
    ∃ f : ℚ[X], IsBelyiPolynomial f ∧ ∀ x ∈ S, f.eval x = 0 ∨ f.eval x = 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨X, isBelyiPolynomial_X, by simp⟩
  · set a := S.min' hne with ha
    set b := S.max' hne with hb
    set d : ℚ := if b - a = 0 then 1 else b - a with hd
    have hdpos : 0 < d := by
      rcases eq_or_ne (b - a) 0 with h | h
      · simp [hd, h]
      · have hab : a ≤ b := S.min'_le_max' hne
        have : 0 < b - a := lt_of_le_of_ne (by linarith) (Ne.symm h)
        simp [hd, h, this]
    set A : ℚ[X] := C d⁻¹ * (X - C a) with hA
    have hAdeg : A.natDegree = 1 := by
      rw [hA, natDegree_mul (by simp [hdpos.ne']) (X_sub_C_ne_zero a), natDegree_C,
        natDegree_X_sub_C]
    have hAnocrit : ∀ z : ℂ, aeval z (derivative A) ≠ 0 := by
      intro z hz
      rw [hA] at hz
      simp only [derivative_mul, derivative_C, derivative_X, zero_mul, zero_add, map_sub] at hz
      have hne0 : (d⁻¹ : ℚ) ≠ 0 := inv_ne_zero hdpos.ne'
      exact hne0 (by simpa using hz)
    have hAbelyi : IsBelyiPolynomial A :=
      ⟨by rw [hAdeg]; omega, fun z hz => absurd hz (hAnocrit z)⟩
    have hAmem : ∀ x ∈ S, 0 ≤ A.eval x ∧ A.eval x ≤ 1 := by
      intro x hx
      have hax : a ≤ x := S.min'_le x hx
      have hxb : x ≤ b := S.le_max' x hx
      have hev : A.eval x = (x - a) / d := by rw [hA]; simp [div_eq_inv_mul]
      rw [hev]
      constructor
      · exact div_nonneg (by linarith) hdpos.le
      · rw [div_le_one hdpos]
        rcases eq_or_ne (b - a) 0 with h | h
        · have : x = a := by
            have : b = a := by linarith
            rw [this] at hxb; linarith
          simp [hd, h, this]
        · simp only [hd, if_neg h]
          linarith
    obtain ⟨g, hgB, hgS, _, _, _⟩ := exists_ratBelyi (S.image (fun x => A.eval x)) (by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hAmem x hx)
    refine ⟨g.comp A, ?_, ?_⟩
    · exact IsBelyiPolynomial.comp hAbelyi.1 hgB (fun z hz => absurd hz (hAnocrit z))
    · intro x hx
      rw [eval_comp]
      exact hgS _ (Finset.mem_image.2 ⟨x, hx, rfl⟩)

end Math2

import Mathlib

/-!
# The elementary Belyi polynomials `x ↦ c · x^m (1-x)^n`

This file develops the basic properties of the polynomials used in Belyi's construction:
for positive naturals `m, n` the polynomial
`B_{m,n}(x) = ((m+n)^(m+n)/(m^m n^n)) · x^m (1-x)^n`
has all of its finite critical values in `{0, 1}`, sends `0, 1` to `0`, sends `m/(m+n)` to `1`,
and maps the unit interval into itself.
-/

set_option maxRecDepth 8000

namespace Math2

open Polynomial

/-- The normalizing constant `(m+n)^(m+n) / (m^m n^n)`. -/
