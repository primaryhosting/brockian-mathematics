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


lemma sum_rot_pinch (M : Matrix (β × γ) (β × γ) ℂ) :
    ∑ k : ZMod (Fintype.card γ),
        (pinch M).submatrix (rotEquiv β k).symm (rotEquiv β k).symm
      = (ptR M) ⊗ₖ (1 : Matrix γ γ ℂ) := by
  classical
  ext p q
  rw [Matrix.sum_apply]
  by_cases hcc : p.2 = q.2
  · have hterm : ∀ k : ZMod (Fintype.card γ),
        ((pinch M).submatrix (rotEquiv β k).symm (rotEquiv β k).symm) p q
          = M (p.1, (rotPerm k).symm p.2) (q.1, (rotPerm k).symm p.2) := by
      intro k
      rw [Matrix.submatrix_apply, rotEquiv_symm_apply, rotEquiv_symm_apply, ← hcc]
      simp [pinch]
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hterm k)]
    rw [sum_rotPerm (fun e => M (p.1, e) (q.1, e)) p.2]
    simp [Matrix.kroneckerMap_apply, Matrix.one_apply, hcc]
  · have hterm : ∀ k : ZMod (Fintype.card γ),
        ((pinch M).submatrix (rotEquiv β k).symm (rotEquiv β k).symm) p q = 0 := by
      intro k
      rw [Matrix.submatrix_apply, rotEquiv_symm_apply, rotEquiv_symm_apply]
      simp only [pinch, Matrix.of_apply, ite_eq_right_iff]
      intro hEq
      exact absurd ((rotPerm k).symm.injective hEq) hcc
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hterm k)]
    simp [Matrix.kroneckerMap_apply, Matrix.one_apply, hcc]

/-! ### Monotonicity of the relative entropy under the partial trace -/

