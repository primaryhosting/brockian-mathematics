/-
  Aristotle target — Euler's theorem on odd perfect numbers (a genuine hard partial
  result toward the ancient odd-perfect-number problem; existence remains OPEN).

  If n is odd and perfect, then n has Euler's form n = p^k * m^2 with p prime,
  p ≡ 1 (mod 4), k ≡ 1 (mod 4), and p ∤ m.
-/
import Mathlib

namespace Brockian.OddPerfectEuler

open ArithmeticFunction


private lemma geom_sum_mod_four {p e : ℕ} (hp : p % 2 = 1)
    (h : (∑ i ∈ Finset.range (e + 1), p ^ i) % 4 = 2) :
    p % 4 = 1 ∧ e % 4 = 1 := by
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  cases hp4 with
  | inl hp1 =>
    refine ⟨hp1, ?_⟩
    have hpi : ∀ i, p ^ i % 4 = 1 := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => simp [pow_succ, Nat.mul_mod, ih, hp1]
    have hsum : (∑ i ∈ Finset.range (e + 1), p ^ i) % 4 = (e + 1) % 4 := by
      simp [Finset.sum_nat_mod, hpi]
    omega
  | inr hp3 =>
    -- p % 4 = 3 case leads to contradiction: sum is 0 or 1 mod 4, never 2
    have hpi : ∀ i, p ^ i % 4 = if i % 2 = 0 then 1 else 3 := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        rw [pow_succ, Nat.mul_mod, ih, hp3]
        split_ifs with hi <;> simp_all [Nat.add_mod]
    -- Now derive contradiction: sum is 0 or 1 mod 4, never 2
    have hsum_cycle : ∀ e, (∑ i ∈ Finset.range (e + 1), p ^ i) % 4 = if e % 2 = 0 then 1 else 0 := by
      intro e
      induction e with
      | zero => simp
      | succ e ih =>
        rw [Finset.sum_range_succ]
        rw [Nat.add_mod, ih, hpi (e + 1)]
        split_ifs <;> omega
    have := hsum_cycle e
    simp_all
    split_ifs at h with he <;> omega

