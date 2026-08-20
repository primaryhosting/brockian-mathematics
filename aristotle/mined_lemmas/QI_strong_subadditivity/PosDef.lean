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


lemma PosDef.conj_unitary {A : Matrix n n ℂ} (hA : A.PosDef) (u : unitary (Matrix n n ℂ)) :
    ((u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ)).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  have hH : ((u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ)).IsHermitian := by
    have hsA : star A = A := hA.1
    have : star ((u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ))
        = (u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ) := by
      simp only [StarMul.star_mul, star_star, mul_assoc, hsA]
    exact this
  refine ⟨hH, ?_⟩
  intro x hx
  have hxx : star (star (u : Matrix n n ℂ) *ᵥ x) ⬝ᵥ A *ᵥ (star (u : Matrix n n ℂ) *ᵥ x)
      = star x ⬝ᵥ ((u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ)) *ᵥ x := by
    rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul]
    simp [star_eq_conjTranspose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, mul_assoc]
  rw [← hxx]
  refine (Matrix.posDef_iff_dotProduct_mulVec.mp hA).2 ?_
  intro hc
  apply hx
  have : (u : Matrix n n ℂ) *ᵥ (star (u : Matrix n n ℂ) *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, u.2.2, Matrix.one_mulVec]
  rw [hc] at this
  simpa using this.symm

