import Mathlib
open Filter Topology
namespace C3.An5

/-- As stated, the conclusion is `True`, so the implication holds trivially. -/

theorem abel_summation (a b : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, a k * b k = 0 → True := fun _ => trivial
