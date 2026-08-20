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


lemma sum_Dsign_conj (M : Matrix (β × γ) (β × γ) ℂ) :
    ∑ s : γ → Bool, (((2 : ℝ) ^ Fintype.card γ)⁻¹ • (Dsign β s * M * star (Dsign β s)))
      = pinch M := by
  classical
  ext p q
  rw [Matrix.sum_apply]
  have hterm : ∀ s : γ → Bool,
      (((2 : ℝ) ^ Fintype.card γ)⁻¹ • (Dsign β s * M * star (Dsign β s))) p q
        = (((2 : ℂ) ^ Fintype.card γ)⁻¹ * M p q) * (sgnC s p.2 * sgnC s q.2) := by
    intro s
    rw [Matrix.smul_apply, Dsign_conj_apply]
    push_cast [Complex.real_smul]
    ring
  rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => hterm s), ← Finset.mul_sum,
    sum_sgnC]
  have h2 : ((2 : ℂ) ^ Fintype.card γ) ≠ 0 := by positivity
  by_cases h : p.2 = q.2
  · rw [if_pos h]
    field_simp
    simp [pinch, h]
  · rw [if_neg h, mul_zero]
    simp [pinch, h]

/-! ### Stage 2 of the twirl: averaging over cyclic shifts -/

section Rot

variable [Nonempty γ]

instance neZeroCardOfNonempty : NeZero (Fintype.card γ) := ⟨Fintype.card_ne_zero⟩

/-- An identification of `γ` with the cyclic group of its own cardinality. -/
