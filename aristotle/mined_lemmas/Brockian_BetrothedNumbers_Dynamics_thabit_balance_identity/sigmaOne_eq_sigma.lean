import Mathlib
import RequestProject.ThabitBalanceIdentity

/-!
# Thabit Balance Identity — Mathlib interface

This file connects the self-contained divisor-sum `sigmaOne` used in
`RequestProject.ThabitBalanceIdentity` with Mathlib's `ArithmeticFunction.sigma 1`, and restates
the Thabit balance identity and the deficient/perfect/abundant comparisons in Mathlib terms.
-/

namespace Brockian.BetrothedNumbers.Dynamics

open ArithmeticFunction

/-- `sigmaOne` is Mathlib's sum-of-divisors function `σ₁`. -/

theorem sigmaOne_eq_sigma (n : ℕ) : sigmaOne n = sigma 1 n := by
  rw [ArithmeticFunction.sigma_one_apply]
  have h1 : n.divisors = (Finset.range (n + 1)).filter (fun d => d != 0 && n % d == 0) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_range, Bool.and_eq_true,
      bne_iff_ne, ne_eq, beq_iff_eq]
    constructor
    · rintro ⟨hd, hn⟩
      have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
      have hd0 : d ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd hd)
      exact ⟨by omega, hd0, Nat.mod_eq_zero_of_dvd hd⟩
    · rintro ⟨_, h0, hd⟩
      exact ⟨Nat.dvd_of_mod_eq_zero hd, by rintro rfl; simp at hd ⊢; omega⟩
  rw [h1, Finset.sum_eq_multiset_sum]
  simp only [sigmaOne, Finset.filter, Finset.range, Multiset.range, Multiset.filter_coe,
    Multiset.map_id', Multiset.sum_coe]
  simp
  rfl

/-- The Thabit sigma criterion, phrased with Mathlib's `σ₁`. -/
