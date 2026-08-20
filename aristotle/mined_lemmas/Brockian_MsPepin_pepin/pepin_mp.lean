import Mathlib
namespace Brockian.MsPepin

/-- For `n ≥ 1`, the Fermat number `F n = 2^(2^n)+1` is `1` mod `4`. -/

private lemma pepin_mp (n : ℕ) (hn : 1 ≤ n) (hp : (2 ^ (2 ^ n) + 1).Prime) :
    (3 : ZMod (2 ^ (2 ^ n) + 1)) ^ (2 ^ (2 ^ n) / 2) = -1 := by
  haveI : Fact (Nat.Prime (2 ^ (2 ^ n) + 1)) := ⟨hp⟩
  have h := legendre_three n hn
  have euler := legendreSym.eq_pow (p := 2 ^ (2 ^ n) + 1) (a := 3)
  rw [h] at euler
  have key : (2 ^ (2 ^ n) + 1) / 2 = 2 ^ (2 ^ n) / 2 := by
    have h2 : 2 ∣ 2 ^ (2 ^ n) := dvd_pow_self 2 (by positivity)
    omega
  rw [key] at euler
  simp at euler
  exact euler.symm

/-- `-1 ≠ 1` in `ZMod (F n)` for `n ≥ 1`, since `F n > 2`. -/
