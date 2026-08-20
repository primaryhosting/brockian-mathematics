import Mathlib
namespace Brockian.PseudoprimesBaseTwo

/-! ### Cipolla's construction

For an odd prime `p ≥ 5` the number `N p = (4 ^ p - 1) / 3 = (2 ^ p - 1) * ((2 ^ p + 1) / 3)`
is a Fermat pseudoprime to base 2. -/

/-- `A p = 2 ^ p - 1`. -/

private lemma two_p_dvd_N_sub_one {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : 2 * p ∣ N p - 1 := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h2 : 2 ∣ N p - 1 := by
    have hNodd : Odd (N p) := N_odd p hodd
    obtain ⟨k, hk⟩ := hNodd
    use k
    rw [hk]
    simp
  have hcoprime : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt Nat.zero_lt_two (by omega))
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcoprime h2 (p_dvd_N_sub_one hp h5)

