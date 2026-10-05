import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma wt_le_wt_union {V W U : Finset X} {δ p : ℝ} {m : ℕ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hp : 0 ≤ p)
    (hWV : W ⊆ V) (hUV : U ⊆ V) (hdisj : Disjoint U W) (hcard : U.card = m) :
    wt V δ W * p ^ m ≤ wt V δ (W ∪ U) * (p / δ) ^ m := by
  have hUW : U ⊆ V \ W := by
    intro y hy
    exact Finset.mem_sdiff.mpr ⟨hUV hy, fun h => (Finset.disjoint_left.mp hdisj hy) h⟩
  have hsplit : (V \ (W ∪ U)).card + m = (V \ W).card := by
    have h1 : V \ (W ∪ U) = (V \ W) \ U := by
      ext y; simp only [Finset.mem_sdiff, Finset.mem_union, not_or]; tauto
    rw [h1, ← hcard]
    exact Finset.card_sdiff_add_card_eq_card hUW
  have hcardU : (W ∪ U).card = W.card + m := by
    rw [Finset.card_union_of_disjoint hdisj.symm, hcard]
  have h1mδ : (0:ℝ) ≤ 1 - δ := by linarith
  set k := (V \ (W ∪ U)).card with hk
  have hleft : wt V δ W * p ^ m = δ ^ W.card * (1 - δ) ^ (k + m) * p ^ m := by
    unfold wt
    rw [← hsplit]
  have hright : wt V δ (W ∪ U) * (p / δ) ^ m = δ ^ W.card * (1 - δ) ^ k * p ^ m := by
    unfold wt
    rw [hcardU, div_pow, ← hk]
    field_simp
    ring
  rw [hleft, hright, pow_add]
  have : (1 - δ) ^ m ≤ 1 := pow_le_one₀ h1mδ (by linarith)
  have hnn : 0 ≤ δ ^ W.card * (1 - δ) ^ k * p ^ m := by positivity
  nlinarith [pow_nonneg h1mδ k, pow_nonneg hp m, pow_nonneg (le_of_lt hδ0) W.card,
    pow_nonneg h1mδ m]

/-- Rewriting a nested sum as a sum over a filtered product. -/
