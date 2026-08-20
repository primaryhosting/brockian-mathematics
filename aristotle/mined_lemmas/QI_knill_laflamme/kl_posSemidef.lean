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

lemma kl_posSemidef {P : Matrix d d ℂ} {E : ι → Matrix d d ℂ} {c : ι → ι → ℂ}
    (hPh : Pᴴ = P) (hPi : P * P = P) (hP0 : P ≠ 0)
    (hKL : ∀ i j, P * (E i)ᴴ * E j * P = c i j • P) : (Matrix.of c).PosSemidef := by
  obtain ⟨v, hv⟩ := exists_mulVec_ne_zero hP0
  set u := P *ᵥ v with hu
  have hPu : P *ᵥ u = u := by rw [hu, mulVec_mulVec, hPi]
  set r : ℝ := ∑ x, ‖u x‖ ^ 2 with hrdef
  have hr : 0 < r := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hv
    refine Finset.sum_pos' (fun i _ => by positivity) ⟨x, Finset.mem_univ x, ?_⟩
    have hne : ‖u x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    positivity
  have hr0 : ((r : ℂ)) ≠ 0 := by exact_mod_cast hr.ne'
  have hru : star u ⬝ᵥ u = (r : ℂ) := dotProduct_star_self_ofReal u
  have hsq : ((Real.sqrt r : ℂ))⁻¹ * ((Real.sqrt r : ℂ))⁻¹ = ((r : ℂ))⁻¹ := by
    rw [← mul_inv]
    norm_cast
    rw [Real.mul_self_sqrt hr.le]
  set A : Matrix d ι ℂ := Matrix.of fun x j => ((Real.sqrt r : ℂ))⁻¹ * (E j *ᵥ u) x with hA
  have hAA : Aᴴ * A = Matrix.of c := by
    ext i j
    simp only [Matrix.mul_apply, conjTranspose_apply, hA, Matrix.of_apply, RCLike.star_def,
      map_mul, map_inv₀, Complex.conj_ofReal]
    have hterm : ∀ x : d, ((Real.sqrt r : ℂ))⁻¹ * (starRingEnd ℂ) ((E i *ᵥ u) x) *
        (((Real.sqrt r : ℂ))⁻¹ * (E j *ᵥ u) x)
        = ((r : ℂ))⁻¹ * ((starRingEnd ℂ) ((E i *ᵥ u) x) * (E j *ᵥ u) x) := by
      intro x; rw [← hsq]; ring
    rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum]
    have hdp : ∑ x, (starRingEnd ℂ) ((E i *ᵥ u) x) * (E j *ᵥ u) x
        = star (E i *ᵥ u) ⬝ᵥ (E j *ᵥ u) := by
      simp [dotProduct]
    rw [hdp, code_inner_apply hPh hKL hPu i j, hru]
    field_simp
  rw [← hAA]
  exact posSemidef_conjTranspose_mul_self A

/-- Unitary diagonalization of a positive semidefinite matrix. -/
