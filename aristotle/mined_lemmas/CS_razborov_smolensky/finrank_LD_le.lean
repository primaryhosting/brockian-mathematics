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

lemma finrank_LD_le (D : ℕ) :
    Module.finrank F (LD F n D) ≤ ∑ i ∈ Finset.range (D + 1), n.choose i := by
  have h1 : Module.finrank F (LD F n D) ≤ (monFinset F n D).card :=
    finrank_span_finset_le_card _
  refine h1.trans ?_
  refine (Finset.card_image_le).trans ?_
  have : ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ D)).card
      = ∑ i ∈ Finset.range (D + 1), n.choose i := by
    have : ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ D))
        = (Finset.range (D + 1)).biUnion
            (fun i => Finset.powersetCard i (Finset.univ : Finset (Fin n))) := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      constructor
      · intro h; exact ⟨S.card, by omega, rfl⟩
      · rintro ⟨i, hi, rfl⟩; omega
    rw [this, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.card_powersetCard]
      simp
    · intro i _ j _ hij
      simp only [Finset.disjoint_left, Finset.mem_powersetCard]
      rintro S ⟨-, rfl⟩ ⟨-, h⟩
      exact hij h
  exact this.le

end CS

