import RequestProject.Circuits
import RequestProject.LowDegree

/-!
# MOD_p is not approximable by low degree functions over a field of characteristic q

This is the second half of Smolensky's argument: if the function `x ↦ ζ^{|x|}`
(`ζ` a primitive `p`-th root of unity in a field `F` of characteristic `q`) agrees
with a function of degree `D` on a set `G` of inputs, then `G` is small.
-/

namespace CS

open Finset

open scoped Classical

variable {F : Type*} [Field F] {n : ℕ}

/-- The monomial `∏_{i ∈ S} ζ^{x_i}` in the transformed variables. -/

lemma mul_mem_LD {D₁ D₂ : ℕ} {f g : (Fin n → Bool) → F}
    (hf : f ∈ LD F n D₁) (hg : g ∈ LD F n D₂) : f * g ∈ LD F n (D₁ + D₂) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      induction hg using Submodule.span_induction with
      | mem g hg =>
          simp only [monFinset, Finset.coe_image, Set.mem_image, Finset.mem_coe,
            Finset.mem_filter] at hf hg
          obtain ⟨S, ⟨-, hS⟩, rfl⟩ := hf
          obtain ⟨T, ⟨-, hT⟩, rfl⟩ := hg
          rw [mon_mul]
          exact mon_mem_LD ((Finset.card_union_le _ _).trans (Nat.add_le_add hS hT))
      | zero => simp
      | add g₁ g₂ _ _ ih₁ ih₂ => rw [mul_add]; exact Submodule.add_mem _ ih₁ ih₂
      | smul a g _ ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ih
  | zero => simp
  | add f₁ f₂ _ _ ih₁ ih₂ => rw [add_mul]; exact Submodule.add_mem _ ih₁ ih₂
  | smul a f _ ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ih

