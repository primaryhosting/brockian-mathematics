/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring, so the required header is
-- repeated verbatim as the module docstring immediately below the import.)

import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QI

open Matrix ComplexOrder

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι]

/-! ## Definitions -/

/-- The **Knill–Laflamme conditions** for a code with orthogonal projector `P` and a set of
error operators `E i`: `P (E i)ᴴ (E j) P = c i j • P` for some matrix of scalars `c`. -/

theorem correctable_imp_klConditions {P : Matrix d d ℂ} {E : ι → Matrix d d ℂ}
    (hPh : Pᴴ = P) (hPi : P * P = P) (hP0 : P ≠ 0) (h : Correctable P E) :
    KLConditions P E := by
  obtain ⟨m, R, hR1, hR2⟩ := h
  have hprop : ∀ (k : Fin m) (i : ι), ∃ t : ℂ, (R k * E i) * P = t • P := by
    intro k i
    refine exists_smul_proj hPi hP0 (fun ψ hψ => ?_)
    rcases eq_or_ne ψ 0 with rfl | hψ0
    · exact ⟨0, by simp⟩
    have hstar : star ψ ᵥ* P = star ψ := by
      conv_lhs => rw [← hPh, ← star_mulVec, hψ]
    have hρ : P * vecMulVec ψ (star ψ) * P = vecMulVec ψ (star ψ) := by
      rw [Matrix.mul_vecMulVec, hψ, Matrix.vecMulVec_mul, hstar]
    have hsum : ∑ p : Fin m × ι, (R p.1 * E p.2) * vecMulVec ψ (star ψ) * (R p.1 * E p.2)ᴴ
        = vecMulVec ψ (star ψ) := by
      rw [Fintype.sum_prod_type]
      exact hR2 _ hρ
    exact exists_smul_of_sum_outer (fun p : Fin m × ι => R p.1 * E p.2) ψ hψ0 hsum (k, i)
  choose lam hlam using hprop
  refine ⟨fun i j => ∑ k, star (lam k i) * lam k j, fun i j => ?_⟩
  have expand : P * (E i)ᴴ * E j * P = ∑ k, ((R k * E i) * P)ᴴ * ((R k * E j) * P) := by
    have h5 : P * (E i)ᴴ * E j * P = P * (E i)ᴴ * (∑ k, (R k)ᴴ * R k) * E j * P := by
      rw [hR1, Matrix.mul_one]
    rw [h5, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [conjTranspose_mul, hPh, Matrix.mul_assoc]
  rw [expand, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hlam k i, hlam k j, conjTranspose_smul, hPh, smul_mul_assoc, Matrix.mul_smul, smul_smul, hPi]

/-! ## The Knill–Laflamme conditions imply correctability -/

omit [DecidableEq d] [Fintype ι] [DecidableEq ι] in
/-- On the code space, the Knill–Laflamme scalars compute the inner products of the erroneous
states. -/
