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


theorem gpow_concave {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (A B : ι → Matrix n n ℂ) (hA : ∀ i ∈ s, (A i).PosDef) (hB : ∀ i ∈ s, (B i).PosSemidef)
    (hAsum : (∑ i ∈ s, w i • A i).PosDef) (m : ℕ) :
    ∑ i ∈ s, w i • gpow m (A i) (B i) ≤ gpow m (∑ i ∈ s, w i • A i) (∑ i ∈ s, w i • B i) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hsum : (∑ i ∈ s, w i • gpow m (A i) (B i)).PosSemidef := by
        refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
          Matrix.PosSemidef.zero ?_
        intro i hi
        exact (gpow_posSemidef (hA i hi) (hB i hi) m).smul (by exact_mod_cast hw i hi)
      calc ∑ i ∈ s, w i • gpow (m + 1) (A i) (B i)
          = ∑ i ∈ s, w i • gmean (A i) (gpow m (A i) (B i)) := by simp
        _ ≤ gmean (∑ i ∈ s, w i • A i) (∑ i ∈ s, w i • gpow m (A i) (B i)) :=
            gmean_concave s w hw A (fun i => gpow m (A i) (B i)) hA
              (fun i hi => gpow_posSemidef (hA i hi) (hB i hi) m) hAsum
        _ ≤ gmean (∑ i ∈ s, w i • A i) (gpow m (∑ i ∈ s, w i • A i) (∑ i ∈ s, w i • B i)) :=
            gmean_mono_right hAsum hsum ih
        _ = gpow (m + 1) (∑ i ∈ s, w i • A i) (∑ i ∈ s, w i • B i) := by simp

/-- The scalar recursion corresponding to `gpow`: `dyseq m a b = a ^ (1 - 2⁻ᵐ) * b ^ (2⁻ᵐ)`. -/
