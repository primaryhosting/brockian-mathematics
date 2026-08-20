import Mathlib
namespace Brockian.PseudoprimesBaseTwo

/-! ### Cipolla's construction

For an odd prime `p ≥ 5` the number `N p = (4 ^ p - 1) / 3 = (2 ^ p - 1) * ((2 ^ p + 1) / 3)`
is a Fermat pseudoprime to base 2. -/

/-- `A p = 2 ^ p - 1`. -/

private lemma p_dvd_N_sub_one {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : p ∣ N p - 1 := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h3N : 3 * N p + 1 = 4 ^ p := three_mul_N p hodd
  have h1 : 1 ≤ N p := le_of_lt (one_lt_N h5)
  have h2 : 3 * (N p - 1) = 4 ^ p - 4 := by omega
  have h4 : p ∣ 4 ^ p - 4 := by
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    have h4p : 4 ≤ 4 ^ p := Nat.le_self_pow hp.ne_zero 4
    have hmod : (4 : ℕ) ≡ 4 ^ p [MOD p] := by
      refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
      push_cast
      exact (ZMod.pow_card (4 : ZMod p)).symm
    exact (Nat.modEq_iff_dvd' h4p).mp hmod
  have hdiv3 : p ∣ 3 * (N p - 1) := h2 ▸ h4
  have hgcd : Nat.Coprime p 3 :=
    hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))
  exact hgcd.dvd_of_dvd_mul_left hdiv3

