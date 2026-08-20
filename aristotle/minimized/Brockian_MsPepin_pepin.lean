import Mathlib
namespace Brockian.MsPepin

/-- For `n ≥ 1`, the Fermat number `F n = 2^(2^n)+1` is `1` mod `4`. -/

private lemma fermat_mod_four (n : ℕ) (hn : 1 ≤ n) : (2 ^ (2 ^ n) + 1) % 4 = 1 := by
  have h : 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
  have h2 : 4 ∣ 2 ^ (2 ^ n) := pow_dvd_pow 2 h
  simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd h2]

/-- For `n ≥ 1`, the Fermat number `F n = 2^(2^n)+1` is `2` mod `3`. -/

private lemma fermat_mod_three (n : ℕ) (hn : 1 ≤ n) : (2 ^ (2 ^ n) + 1) % 3 = 2 := by
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn]
  have h3 : 2 ^ (2 ^ n) = (2 ^ 2) ^ (2 ^ (n - 1)) := by rw [h2, pow_mul]
  rw [h3]
  norm_num at *
  have h4 : 4 ^ 2 ^ (n - 1) % 3 = 1 := by
    have := Nat.pow_mod 4 (2 ^ (n - 1)) 3
    simp [this]
  rw [Nat.add_mod, h4]

/-- `2` is not a square modulo `3`. -/

private lemma legendreSym_three_two : legendreSym 3 (2 : ℤ) = -1 := by decide

/-- `3` is a quadratic nonresidue modulo a prime Fermat number `F n`, `n ≥ 1`. -/

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
