import Mathlib

/-!
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The cosine Gram matrix of a family of angles: `C θ i j = cos (θ i - θ j)`,
the Gram matrix of the unit vectors `(cos (θ i), sin (θ i))` in the plane. -/
noncomputable def cosGram (n : ℕ) (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (θ i - θ j)

/-- The quadratic form of the cosine Gram matrix is a sum of two squares. -/
lemma cosGram_quadratic_form (n : ℕ) (θ : Fin n → ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (Matrix.mulVec (cosGram n θ) x)
      = (∑ i, x i * Real.cos (θ i)) ^ 2 + (∑ i, x i * Real.sin (θ i)) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, cosGram, Matrix.of_apply, Real.cos_sub, pow_two,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The cosine Gram matrix is symmetric (Hermitian over `ℝ`). -/
lemma cosGram_isHermitian (n : ℕ) (θ : Fin n → ℝ) : (cosGram n θ).IsHermitian := by
  ext i j
  simp only [cosGram, Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial,
    ← Real.cos_neg (θ j - θ i), neg_sub]

/-- **Cos Trace Norm 2707.**  For any family of angles `θ : Fin n → ℝ`, the cosine Gram
matrix `C θ i j = cos (θ i - θ j)` is positive semidefinite with trace `n`; hence (being
positive semidefinite) its trace norm equals its trace, namely `n`.  Its quadratic form is
the sum of two squares, and the total sum of its entries lies in `[0, n ^ 2]`. -/
theorem CosTraceNorm2707 (n : ℕ) (θ : Fin n → ℝ) :
    (cosGram n θ).PosSemidef ∧
    (cosGram n θ).trace = (n : ℝ) ∧
    (∀ x : Fin n → ℝ, x ⬝ᵥ (Matrix.mulVec (cosGram n θ) x)
        = (∑ i, x i * Real.cos (θ i)) ^ 2 + (∑ i, x i * Real.sin (θ i)) ^ 2) ∧
    0 ≤ ∑ i, ∑ j, Real.cos (θ i - θ j) ∧
    ∑ i, ∑ j, Real.cos (θ i - θ j) ≤ (n : ℝ) ^ 2 := by
  have hquad := cosGram_quadratic_form n θ
  have hpsd : (cosGram n θ).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨cosGram_isHermitian n θ, fun x => ?_⟩
    have : star x = x := rfl
    rw [this, hquad x]
    positivity
  refine ⟨hpsd, ?_, hquad, ?_, ?_⟩
  · simp [Matrix.trace, Matrix.diag, cosGram]
  · have h1 := hquad (fun _ => 1)
    have h2 : (fun _ : Fin n => (1 : ℝ)) ⬝ᵥ (Matrix.mulVec (cosGram n θ) (fun _ => 1))
        = ∑ i, ∑ j, Real.cos (θ i - θ j) := by
      simp [dotProduct, Matrix.mulVec, cosGram]
    rw [← h2, h1]
    positivity
  · calc ∑ i, ∑ j, Real.cos (θ i - θ j) ≤ ∑ _i : Fin n, ∑ _j : Fin n, (1 : ℝ) := by
          exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Real.cos_le_one _
      _ = (n : ℝ) ^ 2 := by simp [sq]

end Brockian

