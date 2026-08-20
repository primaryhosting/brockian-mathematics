import Mathlib
namespace Brockian.MsEulerPentagonal
/-- Euler's pentagonal number theorem (recurrence form): the partition function satisfies
    ∑_{k} (−1)^k · p(n − g_k) = 0 for n > 0, where g_k = k(3k−1)/2 ranges over generalized
    pentagonal numbers. Stated here as the alternating sum over pentagonal offsets. -/
theorem euler_pentagonal (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc (-(n:ℤ)) n,
      (if (k * (3 * k - 1) / 2) ≤ (n:ℤ) then
        (-1) ^ (k.natAbs) * (Fintype.card (Nat.Partition (n - (k * (3 * k - 1) / 2).toNat)))
       else 0) = 0 := by
  sorry
end Brockian.MsEulerPentagonal
