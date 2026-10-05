/-
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction

/-- Geometric sum identity in `ℕ`, phrased so as to avoid truncated subtraction. -/

lemma prod_bound_of_card_le_three {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hcard : S.card ≤ 3) :
    4 * ∏ p ∈ S, p ≤ 15 * ∏ p ∈ S, (p - 1) := by
  interval_cases h : S.card
  · rw [Finset.card_eq_zero] at h
    subst h; simp
  · rw [Finset.card_eq_one] at h
    obtain ⟨a, rfl⟩ := h
    have ha : a.Prime := hS a (by simp)
    have := ha.two_le
    simp only [Finset.prod_singleton]
    omega
  · rw [Finset.card_eq_two] at h
    obtain ⟨a, b, hab, rfl⟩ := h
    have ha : a.Prime := hS a (by simp)
    have hb : b.Prime := hS b (by simp)
    -- wlog a < b
    have key : ∀ x y : ℕ, x.Prime → y.Prime → x < y →
        4 * (x * y) ≤ 15 * ((x - 1) * (y - 1)) := by
      intro x y hx hy hxy
      have hx2 : 2 ≤ x := hx.two_le
      have hy3 : 3 ≤ y := by omega
      obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
      obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      nlinarith [hx2, hy3, Nat.zero_le (x' * y')]
    rw [Finset.prod_pair hab, Finset.prod_pair hab]
    rcases lt_or_gt_of_ne hab with h1 | h1
    · exact key a b ha hb h1
    · have := key b a hb ha h1
      calc 4 * (a * b) = 4 * (b * a) := by ring
        _ ≤ 15 * ((b - 1) * (a - 1)) := this
        _ = 15 * ((a - 1) * (b - 1)) := by ring
  · rw [Finset.card_eq_three] at h
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := h
    have ha : a.Prime := hS a (by simp)
    have hb : b.Prime := hS b (by simp)
    have hc : c.Prime := hS c (by simp)
    have hprod : ∀ x y z : ℕ, x ≠ y → x ≠ z → y ≠ z →
        ∏ p ∈ ({x, y, z} : Finset ℕ), p = x * (y * z) := by
      intro x y z h1 h2 h3
      rw [Finset.prod_insert (by simp [h1, h2]), Finset.prod_pair h3]
    have hprod' : ∀ x y z : ℕ, x ≠ y → x ≠ z → y ≠ z →
        ∏ p ∈ ({x, y, z} : Finset ℕ), (p - 1) = (x - 1) * ((y - 1) * (z - 1)) := by
      intro x y z h1 h2 h3
      rw [Finset.prod_insert (by simp [h1, h2]), Finset.prod_pair h3]
    have key : ∀ x y z : ℕ, x.Prime → y.Prime → z.Prime → x < y → y < z →
        4 * (x * (y * z)) ≤ 15 * ((x - 1) * ((y - 1) * (z - 1))) := by
      intro x y z hx hy hz h1 h2
      have := four_mul_le_fifteen_mul_three hx hy hz h1 h2
      calc 4 * (x * (y * z)) = 4 * (x * y * z) := by ring
        _ ≤ 15 * ((x - 1) * ((y - 1) * (z - 1))) := this
    -- sort a b c
    have main : ∀ x y z : ℕ, x.Prime → y.Prime → z.Prime → x ≠ y → x ≠ z → y ≠ z →
        4 * ∏ p ∈ ({x, y, z} : Finset ℕ), p ≤ 15 * ∏ p ∈ ({x, y, z} : Finset ℕ), (p - 1) := by
      intro x y z hx hy hz h1 h2 h3
      rw [hprod x y z h1 h2 h3, hprod' x y z h1 h2 h3]
      rcases lt_trichotomy x y with hxy | hxy | hxy
      · rcases lt_trichotomy y z with hyz | hyz | hyz
        · exact key x y z hx hy hz hxy hyz
        · exact absurd hyz h3
        · rcases lt_trichotomy x z with hxz | hxz | hxz
          · have := key x z y hx hz hy hxz hyz
            calc 4 * (x * (y * z)) = 4 * (x * (z * y)) := by ring
              _ ≤ 15 * ((x - 1) * ((z - 1) * (y - 1))) := this
              _ = 15 * ((x - 1) * ((y - 1) * (z - 1))) := by ring
          · exact absurd hxz h2
          · have := key z x y hz hx hy hxz hxy
            calc 4 * (x * (y * z)) = 4 * (z * (x * y)) := by ring
              _ ≤ 15 * ((z - 1) * ((x - 1) * (y - 1))) := this
              _ = 15 * ((x - 1) * ((y - 1) * (z - 1))) := by ring
      · exact absurd hxy h1
      · rcases lt_trichotomy x z with hxz | hxz | hxz
        · have := key y x z hy hx hz hxy hxz
          calc 4 * (x * (y * z)) = 4 * (y * (x * z)) := by ring
            _ ≤ 15 * ((y - 1) * ((x - 1) * (z - 1))) := this
            _ = 15 * ((x - 1) * ((y - 1) * (z - 1))) := by ring
        · exact absurd hxz h2
        · rcases lt_trichotomy y z with hyz | hyz | hyz
          · have := key y z x hy hz hx hyz hxz
            calc 4 * (x * (y * z)) = 4 * (y * (z * x)) := by ring
              _ ≤ 15 * ((y - 1) * ((z - 1) * (x - 1))) := this
              _ = 15 * ((x - 1) * ((y - 1) * (z - 1))) := by ring
          · exact absurd hyz h3
          · have := key z y x hz hy hx hyz hxy
            calc 4 * (x * (y * z)) = 4 * (z * (y * x)) := by ring
              _ ≤ 15 * ((z - 1) * ((y - 1) * (x - 1))) := this
              _ = 15 * ((x - 1) * ((y - 1) * (z - 1))) := by ring
    exact main a b c ha hb hc hab hac hbc

/-- If a positive integer has at most three distinct prime factors then it is not
`4`-abundant: `σ(N) < 4N`. -/
