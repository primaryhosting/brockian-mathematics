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


theorem relEnt_ptR_le {R S : Matrix (β × γ) (β × γ) ℂ} (hR : R.PosDef) (hS : S.PosDef) :
    relEnt (ptR R) (ptR S) ≤ relEnt R S := by
  classical
  have hcardBool : Fintype.card (γ → Bool) = 2 ^ Fintype.card γ := by
    simp [Fintype.card_fun]
  have hpR := pinch_posDef hR
  have hpS := pinch_posDef hS
  -- Stage 1: pinching decreases the relative entropy.
  have step1 : relEnt (pinch R) (pinch S) ≤ relEnt R S := by
    have h := relEnt_convex (ι := γ → Bool) Finset.univ
      (fun _ => ((2 : ℝ) ^ Fintype.card γ)⁻¹) (fun i _ => by positivity)
      (fun s => Dsign β s * R * star (Dsign β s))
      (fun s => Dsign β s * S * star (Dsign β s))
      (fun s _ => PosDef.conj_unitary hR ⟨Dsign β s, Dsign_mem_unitary s⟩)
      (fun s _ => PosDef.conj_unitary hS ⟨Dsign β s, Dsign_mem_unitary s⟩)
      (by rw [sum_Dsign_conj]; exact hpR) (by rw [sum_Dsign_conj]; exact hpS)
    rw [sum_Dsign_conj, sum_Dsign_conj] at h
    have hrhs : ∑ s : γ → Bool, ((2 : ℝ) ^ Fintype.card γ)⁻¹ *
        relEnt (Dsign β s * R * star (Dsign β s)) (Dsign β s * S * star (Dsign β s))
          = relEnt R S := by
      have hcongr : ∀ s : γ → Bool,
          ((2 : ℝ) ^ Fintype.card γ)⁻¹ *
            relEnt (Dsign β s * R * star (Dsign β s)) (Dsign β s * S * star (Dsign β s))
            = ((2 : ℝ) ^ Fintype.card γ)⁻¹ * relEnt R S := by
        intro s
        rw [relEnt_conj_unitary hR hS ⟨Dsign β s, Dsign_mem_unitary s⟩]
      rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => hcongr s), Finset.sum_const,
        Finset.card_univ, hcardBool, nsmul_eq_mul]
      have h2 : ((2 : ℝ) ^ Fintype.card γ) ≠ 0 := by positivity
      push_cast
      field_simp
    rw [hrhs] at h
    exact h
  -- Stage 2: averaging over cyclic shifts.
  have step2 : relEnt ((ptR R) ⊗ₖ (1 : Matrix γ γ ℂ)) ((ptR S) ⊗ₖ (1 : Matrix γ γ ℂ))
      ≤ (Fintype.card γ : ℝ) * relEnt (pinch R) (pinch S) := by
    have hsumR : ∑ k : ZMod (Fintype.card γ), (1 : ℝ) •
        ((pinch R).submatrix (rotEquiv β k).symm (rotEquiv β k).symm)
          = (ptR R) ⊗ₖ (1 : Matrix γ γ ℂ) := by
      simpa using sum_rot_pinch (β := β) R
    have hsumS : ∑ k : ZMod (Fintype.card γ), (1 : ℝ) •
        ((pinch S).submatrix (rotEquiv β k).symm (rotEquiv β k).symm)
          = (ptR S) ⊗ₖ (1 : Matrix γ γ ℂ) := by
      simpa using sum_rot_pinch (β := β) S
    have h := relEnt_convex (ι := ZMod (Fintype.card γ)) Finset.univ (fun _ => (1 : ℝ))
      (fun i _ => zero_le_one)
      (fun k => (pinch R).submatrix (rotEquiv β k).symm (rotEquiv β k).symm)
      (fun k => (pinch S).submatrix (rotEquiv β k).symm (rotEquiv β k).symm)
      (fun k _ => PosDef.submatrix_equiv hpR (rotEquiv β k))
      (fun k _ => PosDef.submatrix_equiv hpS (rotEquiv β k))
      (by rw [hsumR]; exact (ptR_posDef hR).kronecker Matrix.PosDef.one)
      (by rw [hsumS]; exact (ptR_posDef hS).kronecker Matrix.PosDef.one)
    rw [hsumR, hsumS] at h
    refine le_trans h (le_of_eq ?_)
    have hcongr : ∀ k : ZMod (Fintype.card γ), (1 : ℝ) *
        relEnt ((pinch R).submatrix (rotEquiv β k).symm (rotEquiv β k).symm)
          ((pinch S).submatrix (rotEquiv β k).symm (rotEquiv β k).symm)
          = relEnt (pinch R) (pinch S) := by
      intro k
      rw [one_mul, relEnt_submatrix_equiv hpR hpS]
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hcongr k), Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [relEnt_kronR (m := γ) (ptR_posDef hR) (ptR_posDef hS)] at step2
  have hd : (0 : ℝ) < (Fintype.card γ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have := le_trans step2 (by
    exact mul_le_mul_of_nonneg_left step1 hd.le :
      (Fintype.card γ : ℝ) * relEnt (pinch R) (pinch S)
        ≤ (Fintype.card γ : ℝ) * relEnt R S)
  exact le_of_mul_le_mul_left this hd

end Rot

end QI

import RequestProject.SSA.Setup

/-!
# The operator geometric mean

For `A` positive definite and `B` positive semidefinite we define
`gmean A B = A ^ (1/2) * (A ^ (-1/2) * B * A ^ (-1/2)) ^ (1/2) * A ^ (1/2)`, characterised
by `X * A⁻¹ * X = B`, and prove the facts we need:

* `gmean.eq_of`: uniqueness,
* `le_gmean`: maximality among hermitian `X` with `X * A⁻¹ * X ≤ B`,
* `gmean_mono_right`: monotonicity in the second variable,
* `gmean_concave`: joint concavity (Ando's theorem).
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
open Matrix

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

section Basic

/-- Positive definite matrices are invertible as ring elements. -/
