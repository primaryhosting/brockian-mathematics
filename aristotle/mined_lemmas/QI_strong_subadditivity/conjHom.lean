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


noncomputable def conjHom (u : unitary (Matrix n n ℂ)) :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix n n ℂ where
  toFun M := (u : Matrix n n ℂ) * M * star (u : Matrix n n ℂ)
  map_one' := by rw [mul_one, u.2.2]
  map_mul' x y := by
    have h : star (u : Matrix n n ℂ) * (u : Matrix n n ℂ) = 1 := u.2.1
    calc (u : Matrix n n ℂ) * (x * y) * star (u : Matrix n n ℂ)
        = (u : Matrix n n ℂ) * x * (star (u : Matrix n n ℂ) * u) * y *
            star (u : Matrix n n ℂ) := by rw [h]; simp [mul_assoc]
      _ = ((u : Matrix n n ℂ) * x * star (u : Matrix n n ℂ)) *
            ((u : Matrix n n ℂ) * y * star (u : Matrix n n ℂ)) := by simp only [mul_assoc]
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_smul_comm, mul_one, u.2.2]
  map_star' x := by simp only [StarMul.star_mul, star_star, mul_assoc]

