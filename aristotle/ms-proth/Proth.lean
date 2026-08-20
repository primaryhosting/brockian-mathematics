import Mathlib
namespace Brockian.MsProth
/-- Proth's theorem: for N = k·2ⁿ + 1 with k odd and k < 2ⁿ, N is prime iff there is a with
    a^((N−1)/2) ≡ −1 (mod N). -/
theorem proth (k n N : ℕ) (hk : Odd k) (hkn : k < 2 ^ n) (hN : N = k * 2 ^ n + 1) :
    N.Prime ↔ ∃ a : ZMod N, a ^ ((N - 1) / 2) = -1 := by
  sorry
end Brockian.MsProth
