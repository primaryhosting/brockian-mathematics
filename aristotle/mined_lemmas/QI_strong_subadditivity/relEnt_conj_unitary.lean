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


theorem relEnt_conj_unitary {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (u : unitary (Matrix n n ℂ)) :
    relEnt ((u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ))
      ((u : Matrix n n ℂ) * B * star (u : Matrix n n ℂ)) = relEnt A B := by
  rw [relEnt, relEnt, log_conj_unitary hA u, log_conj_unitary hB u]
  set U : Matrix n n ℂ := (u : Matrix n n ℂ) with hU
  set L : Matrix n n ℂ := CFC.log A - CFC.log B with hL
  have h : star U * U = 1 := u.2.1
  have hsub : U * CFC.log A * star U - U * CFC.log B * star U = U * L * star U := by
    rw [hL]; simp [mul_sub, sub_mul]
  rw [hsub]
  have hprod : (U * A * star U) * (U * L * star U) = (U * (A * L)) * star U := by
    calc (U * A * star U) * (U * L * star U)
        = U * A * (star U * U) * L * star U := by simp only [mul_assoc]
      _ = U * (A * L) * star U := by rw [h]; simp [mul_assoc]
  rw [hprod, Matrix.trace_mul_comm, ← mul_assoc, h, one_mul]

/-! ### The embedding `Y ↦ 1 ⊗ Y` -/

