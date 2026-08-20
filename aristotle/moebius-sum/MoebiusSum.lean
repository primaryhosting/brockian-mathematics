import Mathlib
namespace Brockian.MoebiusSum
/-- The defining property of the Möbius function: ∑_{d|n} μ(d) = [n = 1]. -/
theorem moebius_sum (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, ArithmeticFunction.moebius d = if n = 1 then 1 else 0 := by
  sorry
end Brockian.MoebiusSum
