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

lemma yMon_span {ζ : F} (hζ1 : ζ ≠ 1) :
    Submodule.span F (Set.range (yMon ζ (n := n))) = ⊤ := by
  rw [eq_top_iff, ← LD_top (F := F) (n := n), LD]
  refine Submodule.span_le.2 ?_
  intro g hg
  simp only [monFinset, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter] at hg
  obtain ⟨S, -, rfl⟩ := hg
  -- expand the monomial in the `y` variables
  have hne : (ζ - 1) ≠ 0 := sub_ne_zero_of_ne hζ1
  have hpt : ∀ x : Fin n → Bool, ((ζ - 1) ^ S.card * mon F S x)
      = ∑ T ∈ S.powerset, (-1 : F) ^ (S.card - T.card) * yMon ζ T x := by
    intro x
    have h0 : ((ζ - 1) ^ S.card * mon F S x) = ∏ i ∈ S, ((1 + (ζ - 1) * bv F (x i)) + (-1)) := by
      rw [mon]
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by ring
    rw [h0, Finset.prod_add]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.mem_powerset] at hT
    rw [Finset.prod_const, Finset.card_sdiff_of_subset hT]
    rw [yMon]
    ring
  have hfun : ((ζ - 1) ^ S.card) • mon F S
      = ∑ T ∈ S.powerset, ((-1 : F) ^ (S.card - T.card)) • yMon ζ T := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    exact hpt x
  have hmem : ((ζ - 1) ^ S.card) • mon F S ∈ Submodule.span F (Set.range (yMon ζ (n := n))) := by
    rw [hfun]
    exact Submodule.sum_mem _ fun T _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, rfl⟩)
  have : mon F S = ((ζ - 1) ^ S.card)⁻¹ • (((ζ - 1) ^ S.card) • mon F S) := by
    rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hne), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ hmem

/-- **The key step of Smolensky's lower bound.**  If `x ↦ ζ^{|x|}` agrees on `G` with a
function of degree `D`, then every function on `G` agrees with a function of degree
`n/2 + D`, so `G` has at most `∑_{i ≤ n/2 + D} C(n,i)` elements. -/
