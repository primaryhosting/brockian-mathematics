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


lemma sum_sgnC (x y : γ) :
    ∑ s : γ → Bool, sgnC s x * sgnC s y
      = if x = y then ((2 : ℂ) ^ Fintype.card γ) else 0 := by
  classical
  rcases eq_or_ne x y with rfl | hxy
  · simp only [if_pos rfl]
    rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => sgnC_mul_self s x)]
    simp [Finset.card_univ, Fintype.card_fun]
  · rw [if_neg hxy]
    set T : ℂ := ∑ s : γ → Bool, sgnC s x * sgnC s y with hT
    have hstep : ∀ s : γ → Bool,
        sgnC (flipAt x s) x * sgnC (flipAt x s) y = -(sgnC s x * sgnC s y) := by
      intro s
      have h1 : sgnC (flipAt x s) x = -(sgnC s x) := by
        show (if (Function.update s x (!s x)) x then (1 : ℂ) else -1) = _
        rw [Function.update_self]
        unfold sgnC
        by_cases h : s x <;> simp [h]
      have h2 : sgnC (flipAt x s) y = sgnC s y := by
        show (if (Function.update s x (!s x)) y then (1 : ℂ) else -1) = _
        rw [Function.update_of_ne (Ne.symm hxy)]
        rfl
      rw [h1, h2]; ring
    have h3 : T = ∑ s : γ → Bool, sgnC (flipAt x s) x * sgnC (flipAt x s) y :=
      (Equiv.sum_comp (flipAt x) (fun s => sgnC s x * sgnC s y)).symm
    rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => hstep s)] at h3
    rw [Finset.sum_neg_distrib, ← hT] at h3
    linear_combination h3 / 2

/-- The diagonal sign unitary attached to `s`. -/
