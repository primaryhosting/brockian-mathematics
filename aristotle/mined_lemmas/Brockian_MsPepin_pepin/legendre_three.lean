import Mathlib
namespace Brockian.MsPepin

/-- For `n ≥ 1`, the Fermat number `F n = 2^(2^n)+1` is `1` mod `4`. -/

private lemma legendre_three (n : ℕ) (hn : 1 ≤ n)
    [Fact (Nat.Prime (2 ^ (2 ^ n) + 1))] :
    legendreSym (2 ^ (2 ^ n) + 1) 3 = -1 := by
  have hF4 : (2 ^ (2 ^ n) + 1) % 4 = 1 := fermat_mod_four n hn
  have hF3 : (2 ^ (2 ^ n) + 1) % 3 = 2 := fermat_mod_three n hn
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  -- Quadratic reciprocity: `F n ≡ 1 [MOD 4]`, so `(3 / F n) = (F n / 3)`.
  have hqr : legendreSym 3 ((2 ^ (2 ^ n) + 1 : ℕ) : ℤ)
      = legendreSym (2 ^ (2 ^ n) + 1) ((3 : ℕ) : ℤ) :=
    legendreSym.quadratic_reciprocity_one_mod_four hF4 (by norm_num)
  -- `F n ≡ 2 [MOD 3]`, and `2` is not a square mod `3`.
  have hmod : ((2 ^ (2 ^ n) + 1 : ℕ) : ℤ) % 3 = (2 : ℤ) := by
    have : ((2 ^ (2 ^ n) + 1) % 3 : ℕ) = 2 := hF3
    omega
  have h2 : legendreSym 3 ((2 ^ (2 ^ n) + 1 : ℕ) : ℤ) = -1 := by
    rw [legendreSym.mod, show ((3 : ℕ) : ℤ) = (3 : ℤ) from by norm_num, hmod,
      legendreSym_three_two]
  rw [← show ((3 : ℕ) : ℤ) = (3 : ℤ) from by norm_num, ← hqr, h2]

/-- Forward direction of Pépin's test. -/
