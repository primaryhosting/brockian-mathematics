import RequestProject.Places

/-!
# Divisors, Riemann–Roch spaces and their dimensions on the projective line

* `Math2.Divisor K` : divisors on `ℙ¹_K`, i.e. finitely supported `ℤ`-valued functions on the
  set of closed points;
* `Math2.deg D` : the degree of a divisor;
* `Math2.riemannRochSpace D` : the Riemann–Roch space `L(D) = {f : ord_v f ≥ -D v for all v}`;
* `Math2.ell D` : its dimension `ℓ(D)` over `K`.

The main result of this file is `Math2.ell_eq`: `ℓ(D) = max (deg D + 1) 0`.
-/

open Polynomial

noncomputable section

namespace Math2

variable {K : Type*} [Field K]

/-- The degree of a closed point of `ℙ¹_K`: the degree of the corresponding monic irreducible
polynomial, resp. `1` for the point at infinity. -/

theorem riemannRochSpace_eq_map (D : Divisor K) :
    riemannRochSpace D
      = Submodule.map (LinearMap.mulRight K (divFun D)⁻¹) (polySpace K (deg D + 1).toNat) := by
  classical
  set h : RatFunc K := divFun D with hh
  have hne : h ≠ 0 := divFun_ne_zero D
  ext f
  simp only [Submodule.mem_map, LinearMap.mulRight_apply, mem_polySpace, mem_riemannRochSpace]
  constructor
  · rintro (rfl | hf)
    · exact ⟨0, ⟨0, by simp, by simp⟩, by simp⟩
    rcases eq_or_ne f 0 with rfl | hf0
    · exact ⟨0, ⟨0, by simp, by simp⟩, by simp⟩
    · -- `g = f * h` is a polynomial of degree `≤ deg D`
      have hfh : f * h ≠ 0 := mul_ne_zero hf0 hne
      have hordfin : ∀ p : FinitePlace K, 0 ≤ ord (some p) (f * h) := by
        intro p
        rw [ord_mul _ hf0 hne, ord_divFun_finite]
        have := hf (some p)
        omega
      obtain ⟨a, ha⟩ := isPolynomial_of_ord_nonneg hfh hordfin
      have ha0 : a ≠ 0 := by
        intro h0
        rw [h0] at ha
        simp at ha
        exact hfh ha
      have hordinf : ord (none : Place K) (f * h) = ord (none : Place K) f + (D none - deg D) := by
        rw [ord_mul _ hf0 hne, ord_divFun_infty]
      have hdegle : (a.natDegree : ℤ) ≤ deg D := by
        have h1 := hf none
        have h2 : ord (none : Place K) (f * h) = -(a.natDegree : ℤ) := by
          rw [ha, ord_polynomial_infty]
        omega
      refine ⟨f * h, ⟨a, ?_, ha⟩, ?_⟩
      · rw [Polynomial.degree_eq_natDegree ha0]
        have : (a.natDegree : ℤ) < (deg D + 1).toNat := by omega
        exact_mod_cast this
      · field_simp
  · rintro ⟨g, ⟨a, hadeg, rfl⟩, rfl⟩
    rcases eq_or_ne a 0 with rfl | ha0
    · left; simp
    right
    intro v
    have hane : (algebraMap K[X] (RatFunc K) a) ≠ 0 := RatFunc.algebraMap_ne_zero ha0
    have hordv : ord v (algebraMap K[X] (RatFunc K) a * h⁻¹)
        = ord v (algebraMap K[X] (RatFunc K) a) - ord v h := by
      rw [ord_mul v hane (inv_ne_zero hne), ord_inv]
      ring
    have hdeg : (a.natDegree : ℤ) ≤ deg D := by
      have h1 : a.degree = (a.natDegree : ℕ) := Polynomial.degree_eq_natDegree ha0
      rw [h1] at hadeg
      have : a.natDegree < (deg D + 1).toNat := by exact_mod_cast hadeg
      omega
    cases v with
    | none =>
      rw [hordv, ord_polynomial_infty, ord_divFun_infty]
      omega
    | some p =>
      rw [hordv, ord_polynomial_finite, ord_divFun_finite]
      have := mult_nonneg p a
      omega

/-- The dimension of the Riemann–Roch space of `D` on `ℙ¹_K`. -/
