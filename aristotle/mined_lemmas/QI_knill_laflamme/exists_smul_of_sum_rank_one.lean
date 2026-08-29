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

lemma exists_smul_of_sum_rank_one {κ : Type} [Fintype κ] (v : Matrix m (Fin 1) ℂ) (hv : v ≠ 0)
    (u : κ → Matrix m (Fin 1) ℂ) (h : ∑ k, u k * (u k)ᴴ = v * vᴴ) (k : κ) :
    ∃ l : ℂ, u k = l • v := by
  have hfro : fro v ≠ 0 := fun hc => hv ((fro_eq_zero_iff v).mp hc)
  have hs0 : ((fro v : ℂ)) ≠ 0 := by exact_mod_cast hfro
  set s : ℂ := (fro v : ℂ) with hs
  set N : Matrix m m ℂ := 1 - s⁻¹ • (v * vᴴ) with hN
  have hvvv : v * vᴴ * v = s • v := by
    rw [Matrix.mul_assoc, col_mul_one_by_one, conjTranspose_mul_self_apply]
  have hNv : N * v = 0 := by
    rw [hN, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, hvvv, smul_smul,
      inv_mul_cancel₀ hs0, one_smul, sub_self]
  have key : ∑ k, (N * u k) * (N * u k)ᴴ = 0 := by
    have h2 : N * (∑ k, u k * (u k)ᴴ) * Nᴴ = N * (v * vᴴ) * Nᴴ := by rw [h]
    rw [Finset.mul_sum, Finset.sum_mul] at h2
    have h3 : N * (v * vᴴ) * Nᴴ = 0 := by
      rw [← Matrix.mul_assoc, hNv, Matrix.zero_mul, Matrix.zero_mul]
    rw [h3] at h2
    refine h2.symm ▸ ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  have keytr : ∑ k : κ, (fro (N * u k) : ℂ) = 0 := by
    have hc := congrArg Matrix.trace key
    rw [Matrix.trace_sum, Matrix.trace_zero] at hc
    rw [← hc]
    exact Finset.sum_congr rfl fun k _ => (trace_mul_conjTranspose_self (N * u k)).symm
  have keyR : ∑ k : κ, fro (N * u k) = 0 := by
    have hcc : ((∑ k : κ, fro (N * u k) : ℝ) : ℂ) = 0 := by push_cast; exact keytr
    exact_mod_cast hcc
  have hzero : fro (N * u k) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => fro_nonneg _)).mp keyR k (Finset.mem_univ k)
  have hNu : N * u k = 0 := (fro_eq_zero_iff _).mp hzero
  refine ⟨s⁻¹ * ((vᴴ * u k) 0 0), ?_⟩
  rw [hN, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, sub_eq_zero] at hNu
  calc u k = s⁻¹ • (v * vᴴ * u k) := hNu
    _ = s⁻¹ • (((vᴴ * u k) 0 0) • v) := by rw [Matrix.mul_assoc, col_mul_one_by_one]
    _ = (s⁻¹ * ((vᴴ * u k) 0 0)) • v := by rw [smul_smul]

end Columns

section CodeVectors

variable {m : Type} [Fintype m] [DecidableEq m]

/-- The `j`-th column of a square matrix, viewed as a column vector. -/
