import Mathlib
namespace Brockian.MsViete
/-- Viète's formula (finite truncation identity): the product of nested-radical cosine terms
    telescopes — ∏_{k=1}^{n} cos(x/2^k) = sin x / (2^n · sin(x/2^n)) for sin(x/2^n) ≠ 0. -/
theorem viete_product (x : ℝ) (n : ℕ) (h : Real.sin (x / 2 ^ n) ≠ 0) :
    ∏ k ∈ Finset.Icc 1 n, Real.cos (x / 2 ^ k)
      = Real.sin x / (2 ^ n * Real.sin (x / 2 ^ n)) := by
  sorry
end Brockian.MsViete
