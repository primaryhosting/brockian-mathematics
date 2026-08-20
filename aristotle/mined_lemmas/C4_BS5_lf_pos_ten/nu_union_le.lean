import Mathlib
namespace C4.BS5


theorem nu_union_le (G H : Finset ℕ) (p : ℕ) : nu (G ∪ H) p ≤ nu G p + nu H p := by
  unfold nu
  rw [Finset.image_union]
  exact Finset.card_union_le _ _

end C4.BS5

