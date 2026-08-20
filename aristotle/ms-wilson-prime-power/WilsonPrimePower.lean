import Mathlib
namespace Brockian.MsWilsonPrimePower
/-- Gauss's extension of Wilson's theorem: for an odd prime p and k ≥ 1, the product of all
    units of ℤ/(p^k) equals −1. -/
theorem wilson_prime_power (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (hk : 0 < k) :
    (∏ u : (ZMod (p ^ k))ˣ, (u : ZMod (p ^ k))) = -1 := by
  sorry
end Brockian.MsWilsonPrimePower
