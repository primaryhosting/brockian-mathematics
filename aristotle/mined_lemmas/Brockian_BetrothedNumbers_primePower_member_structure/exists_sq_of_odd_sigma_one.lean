import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction Finset

namespace Brockian
namespace BetrothedNumbers

/-- `IsBetrothedPair m n` says that `(m, n)` is a betrothed (quasi-amicable) pair: two distinct
positive integers, each of whose sum of divisors equals `m + n + 1`. -/

theorem exists_sq_of_odd_sigma_one :
    ∀ n : ℕ, n % 2 = 1 → sigma 1 n % 2 = 1 → ∃ r, n = r * r := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hodd hs
    have hn0 : n ≠ 0 := by rintro rfl; simp at hodd
    by_cases hn1 : n = 1
    · exact ⟨1, by simp [hn1]⟩
    · obtain ⟨q, e, t, hq, hsplit, hcop, he1⟩ :
          ∃ q e t : ℕ, q.Prime ∧ q ^ e * t = n ∧ Nat.Coprime (q ^ e) t ∧ 1 ≤ e :=
        ⟨n.minFac, n.factorization n.minFac, n / n.minFac ^ (n.factorization n.minFac),
          Nat.minFac_prime hn1, Nat.ordProj_mul_ordCompl_eq_self n n.minFac,
          (Nat.coprime_ordCompl (Nat.minFac_prime hn1) hn0).pow_left _,
          Nat.Prime.factorization_pos_of_dvd (Nat.minFac_prime hn1) hn0 (Nat.minFac_dvd n)⟩
      have hq2 : q % 2 = 1 := by
        rcases hq.eq_two_or_odd with h | h
        · subst h
          exfalso
          have : 2 ∣ n := hsplit ▸ dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) t
          omega
        · exact h
      have ht0 : 0 < t := by
        rcases Nat.eq_zero_or_pos t with rfl | h
        · simp at hsplit; omega
        · exact h
      have hmul : sigma 1 n = sigma 1 (q ^ e) * sigma 1 t := by
        rw [← hsplit]
        exact isMultiplicative_sigma.map_mul_of_coprime hcop
      have hpe : sigma 1 (q ^ e) % 2 = (e + 1) % 2 := by
        rw [sigma_one_apply_prime_pow hq, geom_sum_mod_two hq2]
      have hodds : Odd (sigma 1 (q ^ e)) ∧ Odd (sigma 1 t) := by
        rw [← Nat.odd_mul, ← hmul, Nat.odd_iff]; exact hs
      have h2 : sigma 1 t % 2 = 1 := Nat.odd_iff.mp hodds.2
      have he : e % 2 = 0 := by
        have := Nat.odd_iff.mp hodds.1; omega
      have htodd : t % 2 = 1 := by
        rcases Nat.even_or_odd t with h | h
        · exfalso
          have h2t : 2 ∣ t := h.two_dvd
          have : 2 ∣ n := hsplit ▸ Dvd.dvd.mul_left h2t _
          omega
        · exact Nat.odd_iff.mp h
      have hqe : 2 ≤ q ^ e := by
        calc 2 ≤ q := hq.two_le
        _ = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ e := Nat.pow_le_pow_right (by omega) he1
      have htlt : t < n := by
        rw [← hsplit]
        calc t = 1 * t := (one_mul t).symm
        _ < q ^ e * t := (Nat.mul_lt_mul_right ht0).mpr (by omega)
      obtain ⟨r, hr⟩ := ih t htlt htodd h2
      refine ⟨q ^ (e / 2) * r, ?_⟩
      have hqq : q ^ (e / 2) * q ^ (e / 2) = q ^ e := by
        rw [← pow_add]; congr 1; omega
      rw [← hsplit, hr, ← hqq]; ring

/-! ### Structure of a prime power member -/

/-- **Hagis–Lord, Proposition 4.** If a prime power `p ^ a` (with `a ≥ 1`) is a member of a
betrothed (quasi-amicable) pair, then `p` is odd, the exponent `a` is odd and greater than `3`,
and the partner is even. -/
