import Mathlib
namespace Brockian.FreshmanDream
/-- The "freshman's dream" modulo a prime: (a+b)^p ≡ a^p + b^p (mod p). -/
theorem freshman_dream (p a b : ℕ) (hp : p.Prime) :
    (a + b) ^ p ≡ a ^ p + b ^ p [MOD p] := by
  sorry
end Brockian.FreshmanDream
