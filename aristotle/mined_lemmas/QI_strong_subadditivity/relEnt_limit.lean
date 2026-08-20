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


theorem relEnt_limit (hA : A.PosDef) (hB : B.PosDef) :
    Tendsto (fun m : ℕ => 2 ^ m * (A.trace.re - Qd m A B)) atTop (𝓝 (relEnt A B)) := by
  classical
  set lam := hA.1.eigenvalues
  set mu := hB.1.eigenvalues
  set c := ovl hA.1 hB.1
  have htr : A.trace.re = ∑ i, ∑ j, c i j * lam i := by
    have h1 : A.trace.re = ∑ i, lam i := by
      rw [hA.1.trace_eq_sum_eigenvalues]; simp; rfl
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, ovl_sum_right hA.1 hB.1 i, one_mul]
  have hrew : ∀ m : ℕ, 2 ^ m * (A.trace.re - Qd m A B)
      = ∑ i, ∑ j, c i j * (2 ^ m * (lam i - dyseq m (lam i) (mu j))) := by
    intro m
    rw [htr, Qd_eval hA hB m, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [relEnt_eq hA.1 hB.1]
  refine Tendsto.congr (fun m => (hrew m).symm) ?_
  refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => ?_
  exact (dyseq_limit (hA.eigenvalues_pos i) (hB.eigenvalues_pos j)).const_mul (c i j)

