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


theorem gmean_concave {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (A B : ι → Matrix n n ℂ) (hA : ∀ i ∈ s, (A i).PosDef) (hB : ∀ i ∈ s, (B i).PosSemidef)
    (hAsum : (∑ i ∈ s, w i • A i).PosDef) :
    ∑ i ∈ s, w i • gmean (A i) (B i) ≤ gmean (∑ i ∈ s, w i • A i) (∑ i ∈ s, w i • B i) := by
  set X := ∑ i ∈ s, w i • gmean (A i) (B i) with hXdef
  have hXpsd : X.PosSemidef := by
    rw [hXdef]
    refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
      Matrix.PosSemidef.zero ?_
    intro i hi
    exact (gmean.posSemidef (hA i hi) (hB i hi)).smul (by exact_mod_cast hw i hi)
  have hXherm : X.IsHermitian := hXpsd.1
  refine le_gmean hAsum hXherm ?_
  rw [← fromBlocks_posSemidef_iff hAsum hXherm]
  have : Matrix.fromBlocks (∑ i ∈ s, w i • A i) X X (∑ i ∈ s, w i • B i)
      = ∑ i ∈ s, w i • Matrix.fromBlocks (A i) (gmean (A i) (B i)) (gmean (A i) (B i)) (B i) := by
    rw [hXdef]
    simp only [Matrix.fromBlocks_smul]
    exact fromBlocks_sum s _ _ _ _
  rw [this]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
    Matrix.PosSemidef.zero ?_
  intro i hi
  refine Matrix.PosSemidef.smul ?_ (by exact_mod_cast hw i hi)
  rw [fromBlocks_posSemidef_iff (hA i hi) (gmean.hermitian (hA i hi) (hB i hi))]
  rw [gmean.mul_inv_mul (hA i hi) (hB i hi)]

/-- Covariance of the geometric mean under congruence by an invertible matrix. -/
