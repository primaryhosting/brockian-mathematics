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


lemma posDef_weighted_sum {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (A : ι → Matrix n n ℂ) (hA : ∀ i ∈ s, (A i).PosDef) :
    (∑ i ∈ s, w i • A i).PosDef := by
  classical
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · show (∑ i ∈ s, w i • A i)ᴴ = _
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Matrix.conjTranspose_smul, (hA i hi).1]
    simp
  · intro x hx
    rw [dotProduct_weighted_sum]
    refine Finset.sum_pos' (fun i hi => ?_) ?_
    · exact le_of_lt (mul_pos (by exact_mod_cast hw i hi)
        ((Matrix.posDef_iff_dotProduct_mulVec.mp (hA i hi)).2 hx))
    · obtain ⟨i, hi⟩ := hs
      exact ⟨i, hi, mul_pos (by exact_mod_cast hw i hi)
        ((Matrix.posDef_iff_dotProduct_mulVec.mp (hA i hi)).2 hx)⟩

/-! ### Reindexing -/

