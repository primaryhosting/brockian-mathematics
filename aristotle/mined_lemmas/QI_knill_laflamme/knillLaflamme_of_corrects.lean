import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped ComplexConjugate
open Matrix

namespace QI

section Frobenius

variable {m n : Type} [Fintype m] [Fintype n]

/-- The squared Frobenius norm of a complex matrix, as a real number. -/

theorem knillLaflamme_of_corrects {P : Matrix m m ℂ} (hP : IsCodeProjector P)
    {E : ι → Matrix m m ℂ} (h : Corrects P E) : KnillLaflammeCondition P E := by
  obtain ⟨κ, hκ, R, hR1, hcorr⟩ := h
  have hscal : ∀ (k : κ) (a : ι), ∃ l : ℂ, (R k * E a) * P = l • P := by
    intro k a
    refine eigen_on_code hP _ ?_
    intro v hv
    by_cases hv0 : v = 0
    · exact ⟨0, by rw [hv0]; simp⟩
    have hvH : vᴴ * P = vᴴ := by
      have h1 : (P * v)ᴴ = vᴴ := by rw [hv]
      rwa [Matrix.conjTranspose_mul, hP.herm] at h1
    have hρ : P * (v * vᴴ) * P = v * vᴴ := by
      simp only [← Matrix.mul_assoc]
      rw [hv, Matrix.mul_assoc, hvH]
    have hsum := hcorr (v * vᴴ) hρ
    have hterm : ∀ (A : Matrix m m ℂ), A * (v * vᴴ) * Aᴴ = (A * v) * (A * v)ᴴ := by
      intro A
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have hprod : ∑ p : κ × ι, ((R p.1 * E p.2) * v) * (((R p.1 * E p.2) * v))ᴴ = v * vᴴ := by
      rw [Fintype.sum_prod_type]
      rw [← hsum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => (hterm _).symm
    exact exists_smul_of_sum_rank_one v hv0 _ hprod (k, a)
  choose lam hlam using hscal
  refine ⟨fun a b => ∑ k, star (lam k a) * lam k b, ?_⟩
  intro a b
  have step : ∀ k : κ, (R k * E a * P)ᴴ * (R k * E b * P)
      = (star (lam k a) * lam k b) • P := by
    intro k
    rw [hlam k a, hlam k b, Matrix.conjTranspose_smul, hP.herm, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hP.idem]
  calc P * (E a)ᴴ * E b * P
      = P * (E a)ᴴ * (∑ k, (R k)ᴴ * R k) * E b * P := by rw [hR1, mul_one]
    _ = ∑ k, (P * (E a)ᴴ * ((R k)ᴴ * R k) * E b * P) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ k, ((R k * E a * P)ᴴ * (R k * E b * P)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP.herm]
        noncomm_ring
    _ = ∑ k, (star (lam k a) * lam k b) • P := by
        exact Finset.sum_congr rfl fun k _ => step k
    _ = (∑ k, star (lam k a) * lam k b) • P := by rw [Finset.sum_smul]

end Forward

section Rotation

variable {m ι : Type} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι]

/-- The error operators rotated by a matrix `U`. -/
