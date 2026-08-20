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


theorem relEnt_convex {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (R S : ι → Matrix n n ℂ) (hR : ∀ i ∈ s, (R i).PosDef) (hS : ∀ i ∈ s, (S i).PosDef)
    (hRsum : (∑ i ∈ s, w i • R i).PosDef) (hSsum : (∑ i ∈ s, w i • S i).PosDef) :
    relEnt (∑ i ∈ s, w i • R i) (∑ i ∈ s, w i • S i) ≤ ∑ i ∈ s, w i * relEnt (R i) (S i) := by
  have hstep : ∀ m : ℕ,
      2 ^ m * ((∑ i ∈ s, w i • R i).trace.re - Qd m (∑ i ∈ s, w i • R i) (∑ i ∈ s, w i • S i))
        ≤ ∑ i ∈ s, w i * (2 ^ m * ((R i).trace.re - Qd m (R i) (S i))) := by
    intro m
    have hcon := Qd_concave s w hw R S hR (fun i hi => (hS i hi).posSemidef) hRsum m
    rw [trace_re_sum]
    have : ∑ i ∈ s, w i * (2 ^ m * ((R i).trace.re - Qd m (R i) (S i)))
        = 2 ^ m * ((∑ i ∈ s, w i * (R i).trace.re) - ∑ i ∈ s, w i * Qd m (R i) (S i)) := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this]
    have h2 : (0:ℝ) ≤ 2 ^ m := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) h2
  refine le_of_tendsto_of_tendsto' (relEnt_limit hRsum hSsum) ?_ hstep
  exact tendsto_finset_sum _ fun i hi => (relEnt_limit (hR i hi) (hS i hi)).const_mul (w i)

end QI

