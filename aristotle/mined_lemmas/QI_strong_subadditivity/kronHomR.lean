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


def kronHomR (n m : Type*) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × m) (n × m) ℂ where
  toFun M := M ⊗ₖ (1 : Matrix m m ℂ)
  map_one' := Matrix.one_kronecker_one
  map_mul' x y := by rw [← Matrix.mul_kronecker_mul, one_mul]
  map_zero' := by simp
  map_add' x y := Matrix.add_kronecker x y 1
  commutes' r := by
    simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker]
  map_star' x := by simp [star_eq_conjTranspose, Matrix.conjTranspose_kronecker]

/-- `Y ↦ 1 ⊗ Y`, as a star algebra homomorphism. -/
