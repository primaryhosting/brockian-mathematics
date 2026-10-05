/-
  RequestProject/ESA.lean

  Essential self-adjointness of the harmonic-oscillator core
  `harmonicOscillatorPMap` (the operator `-d²/dx² + x²` on the Schwartz core of
  `L²(ℝ)`).

  The argument is the classical deficiency-index one.  If `g` is in the domain of
  the adjoint with `T* g = z • g` and `Im z ≠ 0`, then pairing against the Hermite
  functions `hermiteFun n` (which lie in the Schwartz core and satisfy
  `H hermiteFun n = (2n+1) hermiteFun n`) forces `⟪g, hermiteFun n⟫ = 0` for every
  `n`, since `conj z ≠ 2n+1`.  The Hermite functions span every monomial
  `xⁿ e^{-x²/2}`, so all the moments of `x ↦ conj (g x) e^{-x²/2}` vanish, and the
  moment theorem gives `g = 0`.
-/
import RequestProject.Corpus
import RequestProject.Hermite
import RequestProject.Moments

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace

namespace Brockian.Weyl.HarmonicOscillator

open Brockian.Weyl.Operator Brockian.Weyl.SchrodingerMinimal Brockian.Moments

/-! ### Integrability facts for an `L²` function against Gaussian weights -/


theorem poly_gauss_bounded (p : Polynomial ℝ) (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, |x| ^ k * (|p.eval x| * Real.exp (-(x ^ 2 / 2))) ≤ C := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1),
    |p.coeff i| * (((k + i)! : ℝ) * 2 ^ (k + i) + 1), fun x => ?_⟩
  have habs : |p.eval x| ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * |x| ^ i := by
    rw [p.eval_eq_sum_range]
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
    exact Finset.sum_congr rfl fun i _ => by rw [abs_mul, abs_pow]
  have hnn : (0 : ℝ) ≤ |x| ^ k * Real.exp (-(x ^ 2 / 2)) := by positivity
  calc |x| ^ k * (|p.eval x| * Real.exp (-(x ^ 2 / 2)))
      = (|x| ^ k * Real.exp (-(x ^ 2 / 2))) * |p.eval x| := by ring
    _ ≤ (|x| ^ k * Real.exp (-(x ^ 2 / 2))) *
          ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * |x| ^ i := by
        exact mul_le_mul_of_nonneg_left habs hnn
    _ = ∑ i ∈ Finset.range (p.natDegree + 1),
          |p.coeff i| * (|x| ^ (k + i) * Real.exp (-(x ^ 2 / 2))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pow_add]; ring
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1),
          |p.coeff i| * (((k + i)! : ℝ) * 2 ^ (k + i) + 1) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_left (pow_abs_mul_gauss_le (k + i) x) (abs_nonneg _)

/-- The real Gaussian. -/
