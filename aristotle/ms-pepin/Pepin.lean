import Mathlib
namespace Brockian.MsPepin
/-- Pépin's test: the Fermat number F_n = 2^(2^n)+1 (n ≥ 1) is prime iff
    3^((F_n−1)/2) ≡ −1 (mod F_n). -/
theorem pepin (n : ℕ) (hn : 1 ≤ n) :
    (2 ^ (2 ^ n) + 1).Prime ↔
      (3 : ZMod (2 ^ (2 ^ n) + 1)) ^ (2 ^ (2 ^ n) / 2) = -1 := by
  sorry
end Brockian.MsPepin
