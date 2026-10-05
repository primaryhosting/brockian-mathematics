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

lemma rotErr_kl {P : Matrix m m ℂ} {E : ι → Matrix m m ℂ} {c : ι → ι → ℂ}
    (hc : ∀ a b, P * (E a)ᴴ * E b * P = c a b • P) (U : Matrix ι ι ℂ) (k l : ι) :
    P * (rotErr U E k)ᴴ * (rotErr U E l) * P
      = ((Uᴴ * (Matrix.of c) * U) k l) • P := by
  have hleft : P * (rotErr U E k)ᴴ = ∑ a, star (U a k) • (P * (E a)ᴴ) := by
    simp only [rotErr, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Finset.mul_sum,
      Matrix.mul_smul]
  have hright : (rotErr U E l) * P = ∑ b, U b l • (E b * P) := by
    simp only [rotErr, Finset.sum_mul, Matrix.smul_mul]
  have hassoc : P * (rotErr U E k)ᴴ * (rotErr U E l) * P
      = (P * (rotErr U E k)ᴴ) * ((rotErr U E l) * P) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc, hleft, hright, Finset.sum_mul_sum]
  have hterm : ∀ a b : ι, (star (U a k) • (P * (E a)ᴴ)) * (U b l • (E b * P))
      = (star (U a k) * (c a b * U b l)) • P := by
    intro a b
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, hc a b, smul_smul]
    ring_nf
  simp only [hterm, ← Finset.sum_smul]
  congr 1
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun y _ => (mul_assoc _ _ _).symm

