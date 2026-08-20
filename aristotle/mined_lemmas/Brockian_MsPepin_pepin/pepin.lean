import Mathlib
namespace Brockian.MsPepin

/-- For `n ≥ 1`, the Fermat number `F n = 2^(2^n)+1` is `1` mod `4`. -/

theorem pepin (n : ℕ) (hn : 1 ≤ n) :
    (2 ^ (2 ^ n) + 1).Prime ↔
      (3 : ZMod (2 ^ (2 ^ n) + 1)) ^ (2 ^ (2 ^ n) / 2) = -1 :=
  ⟨pepin_mp n hn, pepin_mpr n hn⟩

end Brockian.MsPepin

