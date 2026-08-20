import Mathlib
namespace Brockian.LiftingTheExponent
/-- Lifting-the-exponent lemma (odd prime): if p ∤ a and p ∣ a−b (b ≤ a), then
    v_p(aⁿ − bⁿ) = v_p(a − b) + v_p(n). -/
theorem lte_sub {p a b n : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hab : p ∣ (a - b)) (hna : ¬ p ∣ a) (hn : 0 < n) (hle : b ≤ a) :
    (a ^ n - b ^ n).factorization p = (a - b).factorization p + n.factorization p := by
  sorry
end Brockian.LiftingTheExponent
