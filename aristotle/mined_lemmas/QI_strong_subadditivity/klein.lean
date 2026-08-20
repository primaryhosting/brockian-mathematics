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


theorem klein (hA : A.PosSemidef) (hB : B.PosDef) :
    A.trace.re - B.trace.re ≤ relEnt A B := by
  rw [relEnt_eq hA.1 hB.1]
  have htA : A.trace.re = ∑ i, hA.1.eigenvalues i := by
    rw [hA.1.trace_eq_sum_eigenvalues]
    simp
  have htB : B.trace.re = ∑ j, hB.1.eigenvalues j := by
    rw [hB.1.trace_eq_sum_eigenvalues]
    simp
  rw [htA, htB]
  have hlow : ∀ i, ∑ j, ovl hA.1 hB.1 i j *
      (hA.1.eigenvalues i - hB.1.eigenvalues j) ≤ ∑ j, ovl hA.1 hB.1 i j *
      (hA.1.eigenvalues i * (Real.log (hA.1.eigenvalues i) - Real.log (hB.1.eigenvalues j))) := by
    intro i
    refine Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_left
      (scalar_klein (hA.eigenvalues_nonneg i) (hB.eigenvalues_pos j)) (ovl_nonneg hA.1 hB.1 i j)
  refine le_trans ?_ (Finset.sum_le_sum fun i _ => hlow i)
  have hexp : ∀ i, ∑ j, ovl hA.1 hB.1 i j * (hA.1.eigenvalues i - hB.1.eigenvalues j)
      = hA.1.eigenvalues i - ∑ j, ovl hA.1 hB.1 i j * hB.1.eigenvalues j := by
    intro i
    rw [Finset.sum_congr rfl (fun j _ => mul_sub (ovl hA.1 hB.1 i j) (hA.1.eigenvalues i)
      (hB.1.eigenvalues j))]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ovl_sum_right hA.1 hB.1 i, one_mul]
  rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_sub_distrib]
  have hswap : ∑ i, ∑ j, ovl hA.1 hB.1 i j * hB.1.eigenvalues j = ∑ j, hB.1.eigenvalues j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, ovl_sum_left hA.1 hB.1 j, one_mul]
  rw [hswap]

end QI

import RequestProject.SSA.Setup

/-!
# Spectral formulas for traces of functional calculi

For hermitian matrices `A`, `B` with eigenvalues `λ i`, `μ j` and eigenvector unitaries `U`, `V`,
we have `Tr (f A * g B) = ∑ i j, f (λ i) * g (μ j) * c i j` with `c i j = |(U* V) i j|²`
a doubly stochastic matrix of overlaps.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

section trace

