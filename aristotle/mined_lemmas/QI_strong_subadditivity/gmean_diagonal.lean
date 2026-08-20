import RequestProject.SSA.PartialTrace

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header comment above has to follow the `import` line: Lean requires `import` commands to
come first in a file.)

The von Neumann entropy `S(A) = -Tr (A log A)` of a positive definite matrix on a threefold
tensor product `α ⊗ β ⊗ γ` satisfies the Lieb–Ruskai inequality

`S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`.

The proof goes through Lindblad's joint convexity of the Umegaki relative entropy
(itself deduced from Ando's joint concavity of the operator geometric mean) and the
resulting monotonicity of the relative entropy under partial traces.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Kronecker
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

/-! ### Relative entropy against `1 ⊗ Y` -/


lemma gmean_diagonal {a b : n → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 ≤ b i) :
    gmean (Matrix.diagonal fun i => (a i : ℂ)) (Matrix.diagonal fun i => (b i : ℂ))
      = Matrix.diagonal fun i => ((Real.sqrt (a i * b i) : ℝ) : ℂ) := by
  have hApos : (Matrix.diagonal fun i => (a i : ℂ)).PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    exact_mod_cast ha i
  refine gmean.eq_of hApos ?_ ?_
  · rw [Matrix.posSemidef_diagonal_iff]
    intro i
    have : (0:ℝ) ≤ Real.sqrt (a i * b i) := Real.sqrt_nonneg _
    exact_mod_cast this
  · have hai : ∀ i, (a i : ℂ) ≠ 0 := by
      intro i
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt (ha i)
    have hdinv : (Matrix.diagonal fun i => (a i : ℂ))⁻¹
        = Matrix.diagonal fun i => ((a i : ℂ))⁻¹ := by
      refine Matrix.inv_eq_right_inv ?_
      rw [Matrix.diagonal_mul_diagonal]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (hai i)
    rw [hdinv, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    have hsq : (Real.sqrt (a i * b i) : ℂ) * (Real.sqrt (a i * b i) : ℂ)
        = ((a i * b i : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (mul_nonneg (ha i).le (hb i))]
    calc (Real.sqrt (a i * b i) : ℂ) * ((a i : ℂ))⁻¹ * (Real.sqrt (a i * b i) : ℂ)
        = ((Real.sqrt (a i * b i) : ℂ) * (Real.sqrt (a i * b i) : ℂ)) * ((a i : ℂ))⁻¹ := by
          ring
      _ = ((a i * b i : ℝ) : ℂ) * ((a i : ℂ))⁻¹ := by rw [hsq]
      _ = (b i : ℂ) := by
          push_cast
          rw [mul_comm ((a i : ℂ)) ((b i : ℂ)), mul_assoc, mul_inv_cancel₀ (hai i), mul_one]

end QI

import RequestProject.SSA.Spectral

/-!
# Von Neumann entropy and relative entropy

`vnEnt A = -Tr (A log A)` and `relEnt A B = Tr (A (log A - log B))`, together with their
spectral formulas and Klein's inequality.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A B : Matrix n n ℂ}

/-- Von Neumann entropy `-Tr (A log A)`. -/
