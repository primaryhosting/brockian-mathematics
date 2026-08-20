import Mathlib
namespace Brockian.MsPepin

/-- For `n ≥ 1`, the Fermat number `F n = 2^(2^n)+1` is `1` mod `4`. -/

private lemma neg_one_ne_one_fermat (n : ℕ) (hn : 1 ≤ n) :
    (-1 : ZMod (2 ^ (2 ^ n) + 1)) ≠ 1 := by
  have hmod : (2 : ℕ) < 2 ^ (2 ^ n) + 1 := by
    have h1 : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have : 2 ^ 2 ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by norm_num) (by simpa using h1)
    omega
  haveI : Fact (2 < 2 ^ (2 ^ n) + 1) := ⟨hmod⟩
  exact ZMod.neg_one_ne_one

/-- If `3 ^ (F n / 2) = -1` then `3 ^ (F n - 1) = 1`. -/
