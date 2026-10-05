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

lemma orApprox_correct {k ℓ q : ℕ} (hq : q.Prime) [CharP F q]
    (g : Fin k → (Fin n → Bool) → F) (s : Fin ℓ → Finset (Fin k)) (x : Fin n → Bool)
    (bl : Fin k → Bool) (hx : ∀ i, g i x = bv F (bl i))
    (hs : ∀ i0, bl i0 = true → ∃ j, ¬ (q ∣ ((s j).filter (fun i => bl i = true)).card)) :
    orApprox q g s x = bv F (decide (∃ i, bl i = true)) := by
  have hq2 := hq.two_le
  rw [orApprox_apply]
  have hsum : ∀ j : Fin ℓ, (∑ i ∈ s j, g i x)
      = ((((s j).filter (fun i => bl i = true)).card : ℕ) : F) := by
    intro j
    rw [← sum_bv (F := F)]
    exact Finset.sum_congr rfl fun i _ => hx i
  by_cases hex : ∃ i, bl i = true
  · obtain ⟨i0, hi0⟩ := hex
    obtain ⟨j, hj⟩ := hs i0 hi0
    have : ∏ j : Fin ℓ, (1 - (∑ i ∈ s j, g i x) ^ (q - 1)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      rw [hsum j, natCast_pow_char hq, if_neg hj, sub_self]
    rw [this]
    have hex' : ∃ i, bl i = true := ⟨i0, hi0⟩
    simp [bv, hex']
  · push_neg at hex
    have hall : ∀ j : Fin ℓ, ((s j).filter (fun i => bl i = true)) = ∅ := by
      intro j
      refine Finset.filter_eq_empty_iff.2 fun i _ => ?_
      simp [hex i]
    have : ∏ j : Fin ℓ, (1 - (∑ i ∈ s j, g i x) ^ (q - 1)) = 1 := by
      refine Finset.prod_eq_one fun j _ => ?_
      rw [hsum j, hall j]
      simp only [Finset.card_empty, Nat.cast_zero]
      rw [zero_pow (by omega)]
      ring
    rw [this]
    have : ¬ ∃ i, bl i = true := by push_neg; exact hex
    simp [bv, this]

/-! ### The averaging (union bound) step for an OR gate -/

