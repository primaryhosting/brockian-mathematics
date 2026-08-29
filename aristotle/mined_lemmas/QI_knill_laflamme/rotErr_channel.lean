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

lemma rotErr_channel {E : ι → Matrix m m ℂ} (U : Matrix ι ι ℂ) (hU : U * Uᴴ = 1)
    (ρ : Matrix m m ℂ) :
    ∑ k, rotErr U E k * ρ * (rotErr U E k)ᴴ = ∑ a, E a * ρ * (E a)ᴴ := by
  have hexp : ∀ k : ι, rotErr U E k * ρ * (rotErr U E k)ᴴ
      = ∑ a, ∑ b, (U a k * star (U b k)) • (E a * ρ * (E b)ᴴ) := by
    intro k
    simp only [rotErr, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Finset.sum_mul,
      Matrix.smul_mul, Finset.mul_sum, Matrix.mul_smul, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm (star (U b k)) (U a k)]
  simp only [hexp]
  rw [Finset.sum_comm]
  have : ∀ a : ι, ∑ k, ∑ b, (U a k * star (U b k)) • (E a * ρ * (E b)ᴴ)
      = ∑ b, ((U * Uᴴ) a b) • (E a * ρ * (E b)ᴴ) := by
    intro a
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [this, hU, Matrix.one_apply]

end Rotation

section Aux

variable {m : Type} [Fintype m] [DecidableEq m]

