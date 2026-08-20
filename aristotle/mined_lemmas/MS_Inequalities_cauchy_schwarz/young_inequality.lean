import Mathlib
open Finset
namespace MS.Inequalities

theorem young_inequality (a b p q : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) : a * b ≤ a ^ p / p + b ^ q / q :=
  Real.young_inequality_of_nonneg ha hb
    (Real.holderConjugate_iff.2 ⟨hp, by rw [← one_div, ← one_div]; exact hpq⟩)
end MS.Inequalities

