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


def reindHom (e : n ≃ m) : Matrix n n ℂ →⋆ₐ[ℂ] Matrix m m ℂ where
  toFun M := M.submatrix e.symm e.symm
  map_one' := Matrix.submatrix_one_equiv e.symm
  map_mul' x y := (Matrix.submatrix_mul_equiv x y _ _ _).symm
  map_zero' := rfl
  map_add' x y := rfl
  commutes' r := by
    ext i j
    simp [Matrix.submatrix_apply, Algebra.algebraMap_eq_smul_one, Matrix.one_apply]
  map_star' x := rfl

