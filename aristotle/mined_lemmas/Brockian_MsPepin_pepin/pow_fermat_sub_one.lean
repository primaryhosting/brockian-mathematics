import Mathlib
namespace Brockian.MsPepin

/-- For `n ≥ 1`, the Fermat number `F n = 2^(2^n)+1` is `1` mod `4`. -/

private lemma pow_fermat_sub_one (n : ℕ)
    (h : (3 : ZMod (2 ^ (2 ^ n) + 1)) ^ (2 ^ (2 ^ n) / 2) = -1) :
    (3 : ZMod (2 ^ (2 ^ n) + 1)) ^ (2 ^ (2 ^ n) + 1 - 1) = 1 := by
  have hsplit : 2 ^ (2 ^ n) + 1 - 1 = 2 ^ (2 ^ n) / 2 + 2 ^ (2 ^ n) / 2 := by
    obtain ⟨k, hk⟩ : 2 ∣ 2 ^ (2 ^ n) := dvd_pow_self 2 (by positivity)
    omega
  rw [hsplit, pow_add, h]
  ring

/-- The only prime dividing `F n - 1 = 2 ^ (2 ^ n)` is `2`, and
`3 ^ ((F n - 1) / 2) = -1 ≠ 1`. -/
