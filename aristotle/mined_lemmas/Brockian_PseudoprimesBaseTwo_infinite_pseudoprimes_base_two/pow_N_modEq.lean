import Mathlib
namespace Brockian.PseudoprimesBaseTwo

/-! ### Cipolla's construction

For an odd prime `p ≥ 5` the number `N p = (4 ^ p - 1) / 3 = (2 ^ p - 1) * ((2 ^ p + 1) / 3)`
is a Fermat pseudoprime to base 2. -/

/-- `A p = 2 ^ p - 1`. -/

private lemma pow_N_modEq {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    2 ^ (N p) ≡ 2 [MOD N p] := by
  obtain ⟨k, hk⟩ := N_eq hp h5
  have h2p : 2 ^ (2 * p) ≡ 1 [MOD N p] := two_pow_two_mul_modEq (hp.odd_of_ne_two (by omega))
  calc 2 ^ (N p) = 2 ^ (2 * p * k + 1) := by rw [hk]
    _ = (2 ^ (2 * p)) ^ k * 2 := by ring
    _ ≡ 1 ^ k * 2 [MOD N p] := by gcongr
    _ = 2 := by ring

/-- Cipolla: there are infinitely many Fermat pseudoprimes to base 2
    (composite n > 1 with 2^n ≡ 2 mod n). -/
