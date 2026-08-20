import Mathlib
namespace Brockian.MsGaussLucas

open Polynomial

/-- The conjugate of `u⁻¹` is the positive real multiple `(normSq u)⁻¹` of `u`. -/

private lemma sum_inv_eq_zero_of_isRoot_derivative {n : ℕ} (p : ℂ[X]) (a : ℂ) (ha : a ≠ 0)
    (r : Fin n → ℂ) (hfac : p = C a * ∏ i, (X - C (r i))) (z : ℂ)
    (hz : p.derivative.IsRoot z) (hpz : ¬ p.IsRoot z) :
    ∑ i, (z - r i)⁻¹ = 0 := by
  -- Rewrite using hfac
  rw [hfac] at hz hpz
  simp only [IsRoot, eval_mul, eval_C] at hz hpz
  -- Let P = ∏ (X - r i), so p = a * P and p' = a * P'
  set P : ℂ[X] := ∏ i, (X - C (r i)) with hP
  -- The derivative p' = a * P' (since a is constant)
  rw [Polynomial.derivative_C_mul] at hz
  -- So P'(z) = 0 (since a ≠ 0)
  have hPz : P.eval z ≠ 0 := by
    intro h
    apply hpz
    simp [h]
  have hdPz : (Polynomial.derivative P).eval z = 0 := by
    rw [eval_mul, eval_C] at hz
    exact (mul_eq_zero.mp hz).resolve_left ha
  -- Key identity: (derivative P).eval z = P.eval z * ∑ (z - r i)⁻¹
  have key : ∀ (m : ℕ) (s : Fin m → ℂ) (w : ℂ) (hne : ∀ i, w ≠ s i),
      (Polynomial.derivative (∏ i : Fin m, (X - C (s i)))).eval w =
      (∏ i : Fin m, (X - C (s i))).eval w * ∑ i : Fin m, (w - s i)⁻¹ := by
    intro m
    induction' m with m ih
    · intro s w; simp
    · intro s w hne
      let s' : Fin m → ℂ := fun i => s (Fin.succ i)
      have hne0 : w ≠ s 0 := hne 0
      have hn' : ∀ i : Fin m, w ≠ s' i := fun i => hne i.succ
      have hprod_split : ∏ i : Fin (m + 1), (X - C (s i)) = (X - C (s 0)) * ∏ i : Fin m, (X - C (s' i)) := by
        rw [Fin.prod_univ_succ]
      have hderiv_split : derivative (∏ i : Fin (m + 1), (X - C (s i))) =
          (∏ i : Fin m, (X - C (s' i))) + (X - C (s 0)) * derivative (∏ i : Fin m, (X - C (s' i))) := by
        rw [hprod_split, derivative_mul]
        simp [derivative_sub, derivative_X, derivative_C]
      have hsum_split : ∑ i : Fin (m + 1), (w - s i)⁻¹ = (w - s 0)⁻¹ + ∑ i : Fin m, (w - s' i)⁻¹ := by
        rw [Fin.sum_univ_succ]
      have heval_split : (∏ i : Fin (m + 1), (X - C (s i))).eval w = (w - s 0) * (∏ i : Fin m, (X - C (s' i))).eval w := by
        rw [hprod_split, Polynomial.eval_mul]
        simp
      rw [hderiv_split, Polynomial.eval_add, Polynomial.eval_mul]
      simp only [Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C]
      rw [heval_split, hsum_split]
      have ih' := ih s' w hn'
      rw [ih']
      field_simp [sub_ne_zero.mpr hne0]
  have hne : ∀ i, z ≠ r i := by
    intro i hi
    apply hpz
    rw [hP]
    simp only [hi]
    simp [Polynomial.eval_prod]
    right
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by ring)
  have key_applied := key n r z hne
  rw [key_applied] at hdPz
  simp only [mul_eq_zero] at hdPz
  exact hdPz.resolve_left hPz

/-- The Gauss–Lucas theorem: every root of the derivative p' lies in the convex hull of the roots
    of p, for a nonconstant complex polynomial p. -/
