/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

variable {n m : ℕ}

/-! ## Definitions -/

/-- `P` is (the matrix of) an orthogonal projection onto a nonzero code subspace. -/
structure IsCode (P : Matrix (Fin n) (Fin n) ℂ) : Prop where
  herm : Pᴴ = P
  idem : P * P = P
  ne_zero : P ≠ 0

/-- The Knill–Laflamme conditions for a code with projection `P` and error operators `E`:
there is a matrix of scalars `c` with `P Eₐ† E_b P = c a b • P`. -/

theorem kraus_scalar {ι : Type} [Fintype ι] (A : ι → Matrix (Fin n) (Fin n) ℂ) (ψ : Fin n → ℂ)
    (h : ∑ j, A j * vecMulVec ψ (star ψ) * (A j)ᴴ = vecMulVec ψ (star ψ)) (j : ι) :
    ∃ t : ℂ, A j *ᵥ ψ = t • ψ := by
  rcases eq_or_ne ψ 0 with hψ | hψ
  · exact ⟨0, by simp [hψ]⟩
  refine scalar_of_orth _ ψ hψ ?_
  intro phi hphi
  have h2 := congrArg (fun M => star phi ⬝ᵥ (M *ᵥ phi)) h
  simp only [Matrix.sum_mulVec, dotProduct_sum, conj_vecMulVec, quad_vecMulVec] at h2
  have hz2 : star ψ ⬝ᵥ phi = 0 := by
    rw [star_dotProduct_comm phi ψ, hphi]; simp
  rw [hphi, hz2] at h2
  simp only [mul_zero] at h2
  have h3 : ∀ i : ι, (star phi ⬝ᵥ A i *ᵥ ψ) * (star (A i *ᵥ ψ) ⬝ᵥ phi)
      = ((Complex.normSq (star phi ⬝ᵥ A i *ᵥ ψ) : ℝ) : ℂ) := by
    intro i
    rw [star_dotProduct_comm phi (A i *ᵥ ψ), Complex.mul_conj]
  rw [Finset.sum_congr rfl (fun i _ => h3 i)] at h2
  have h5 : (∑ i, Complex.normSq (star phi ⬝ᵥ A i *ᵥ ψ) : ℝ) = 0 := by
    exact_mod_cast (by push_cast; exact h2 :
      ((∑ i, Complex.normSq (star phi ⬝ᵥ A i *ᵥ ψ) : ℝ) : ℂ) = 0)
  have h6 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)).1 h5 j
    (Finset.mem_univ j)
  simpa using h6

/-- An operator which acts as a scalar on every vector of the range of the projection `P`
acts as a fixed scalar on the whole range. -/
