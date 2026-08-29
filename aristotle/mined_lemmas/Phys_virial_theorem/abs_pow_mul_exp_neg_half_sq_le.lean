import RequestProject.Main

/-!
# A concrete instance of the virial theorem

The hypotheses of `Phys.virial_theorem` are satisfiable: we check them for the
ground state `ψ(x) = π^(-1/4) exp(-x²/2)` of the harmonic oscillator
`V(x) = x²/2`, with energy `E = 1/2`, and deduce the virial identity
`2⟨T⟩ = ⟨x ∂ₓV⟩ = 2⟨V⟩` for that state.
-/

namespace Phys

open MeasureTheory Filter Topology Real

/-- `exp (-x²/2)` squared is `exp (-x²)`. -/

theorem abs_pow_mul_exp_neg_half_sq_le (n : ℕ) (x : ℝ) :
    |x| ^ n * Real.exp (-x ^ 2 / 2) ≤ 1 + 2 ^ n * (Nat.factorial n : ℝ) := by
  have hexp_pos : (0 : ℝ) < Real.exp (-x ^ 2 / 2) := Real.exp_pos _
  have hexp_le_one : Real.exp (-x ^ 2 / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg x]
  -- `|x|ⁿ ≤ 1 + (x²)ⁿ`
  have hxn : |x| ^ n ≤ 1 + (x ^ 2) ^ n := by
    rcases le_or_gt |x| 1 with h | h
    · have : |x| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg x) h
      nlinarith [pow_nonneg (sq_nonneg x) n]
    · have h1 : |x| ^ n ≤ (|x| ^ 2) ^ n :=
        pow_le_pow_left₀ (abs_nonneg x) (by nlinarith) n
      have h2 : (|x| ^ 2) ^ n = (x ^ 2) ^ n := by rw [sq_abs]
      nlinarith [h1, h2]
  -- `(x²)ⁿ ≤ 2ⁿ n! exp (x²/2)`
  have hfac : (x ^ 2) ^ n ≤ 2 ^ n * (Nat.factorial n : ℝ) * Real.exp (x ^ 2 / 2) := by
    have h := Real.pow_div_factorial_le_exp (x ^ 2 / 2) (by positivity) n
    have hfac_pos : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have h' : (x ^ 2 / 2) ^ n ≤ (Nat.factorial n : ℝ) * Real.exp (x ^ 2 / 2) := by
      rw [div_le_iff₀ hfac_pos] at h
      linarith [h]
    have hpow : (x ^ 2) ^ n = 2 ^ n * (x ^ 2 / 2) ^ n := by
      rw [div_pow, ← mul_div_assoc]
      field_simp
    rw [hpow]
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    nlinarith [h']
  have hmul : Real.exp (x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) = 1 := by
    rw [← Real.exp_add, show x ^ 2 / 2 + -x ^ 2 / 2 = 0 by ring, Real.exp_zero]
  calc |x| ^ n * Real.exp (-x ^ 2 / 2)
      ≤ (1 + 2 ^ n * (Nat.factorial n : ℝ) * Real.exp (x ^ 2 / 2)) * Real.exp (-x ^ 2 / 2) := by
        have := hxn.trans (by linarith [hfac] : 1 + (x ^ 2) ^ n
          ≤ 1 + 2 ^ n * (Nat.factorial n : ℝ) * Real.exp (x ^ 2 / 2))
        exact mul_le_mul_of_nonneg_right this hexp_pos.le
    _ = Real.exp (-x ^ 2 / 2) + 2 ^ n * (Nat.factorial n : ℝ) := by
        rw [add_mul, one_mul, mul_assoc, hmul, mul_one]
    _ ≤ 1 + 2 ^ n * (Nat.factorial n : ℝ) := by linarith

/-- `xⁿ exp (-x²)` is integrable on the line. -/
