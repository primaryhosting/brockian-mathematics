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


theorem trace_cfc_mul_cfc (hA : A.IsHermitian) (hB : B.IsHermitian) (f g : ℝ → ℝ) :
    (cfc f A * cfc g B).trace
      = ∑ i, ∑ j, ((f (hA.eigenvalues i) * g (hB.eigenvalues j) * ovl hA hB i j : ℝ) : ℂ) := by
  classical
  set U : Matrix n n ℂ := ↑hA.eigenvectorUnitary with hUdef
  set V : Matrix n n ℂ := ↑hB.eigenvectorUnitary with hVdef
  set W : Matrix n n ℂ := star U * V with hWdef
  have hUU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hA.eigenvectorUnitary.2
  have hUU' : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hA.eigenvectorUnitary.2
  have hVV : V * star V = 1 := Matrix.mem_unitaryGroup_iff.1 hB.eigenvectorUnitary.2
  have hcfcA : cfc f A = U * diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) * star U := by
    rw [hA.cfc_eq f, Matrix.IsHermitian.cfc]
    rfl
  have hcfcB : cfc g B = V * diagonal (fun j => ((g (hB.eigenvalues j) : ℝ) : ℂ)) * star V := by
    rw [hB.cfc_eq g, Matrix.IsHermitian.cfc]
    rfl
  rw [hcfcA, hcfcB, trace_conj_diag_pair]
  rfl

end QI

import RequestProject.SSA.Entropy

/-!
# Continuity of the von Neumann entropy

`vnEnt A = Tr (negMulLog A)` for hermitian `A`, and `negMulLog` is continuous on all of `ℝ`,
so the von Neumann entropy is continuous on hermitian matrices.  This is what allows the
strong subadditivity inequality to be extended from positive definite matrices to arbitrary
positive semidefinite ones.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Matrix Filter

set_option maxHeartbeats 1000000

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace of a functional calculus is the sum of the values on the eigenvalues. -/
