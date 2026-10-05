/-
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Real

/-- Auxiliary: `((b : ℝ) ^ k) ^ (t : ℝ) = ((b : ℝ) ^ (t : ℝ)) ^ k` (rpow of a natural power). -/

theorem master_recurrence_pow_bound
    (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b)
    (eps C T₀ : ℝ) (heps : 0 < eps) (hC : 0 < C) (hT₀ : 0 < T₀)
    (f T : ℕ → ℝ)
    (hf0 : ∀ k, 0 ≤ f k)
    (hf : ∀ k, f k ≤ C * ((b : ℝ) ^ k) ^ (Real.logb b a - eps))
    (hTbase : T 0 = T₀)
    (hTrec : ∀ k, T (k + 1) = a * T k + f (k + 1)) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ,
      c₁ * ((b : ℝ) ^ k) ^ (Real.logb b a) ≤ T k ∧
        T k ≤ c₂ * ((b : ℝ) ^ k) ^ (Real.logb b a) := by
  have hb1 : (1 : ℕ) < b := lt_of_lt_of_le one_lt_two hb
  have hbR : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hbR
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < (a : ℝ) := lt_of_lt_of_le zero_lt_one haR
  set r : ℝ := (b : ℝ) ^ (-eps) with hr_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos hb0 _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hbR (neg_neg_iff_pos.mpr heps)
  -- the critical power at `n = b ^ k`
  have hcrit : ∀ k : ℕ, ((b : ℝ) ^ k) ^ (Real.logb b a) = (a : ℝ) ^ k :=
    fun k => rpow_logb_pow ha hb1 k
  -- the bound on `f`
  have hfk : ∀ k : ℕ, f k ≤ C * ((a : ℝ) ^ k * r ^ k) := by
    intro k
    refine (hf k).trans (le_of_eq ?_)
    congr 1
    rw [rpow_natPow b hb0 k, Real.rpow_sub hb0, Real.rpow_logb hb0 (ne_of_gt hbR)
      (by exact_mod_cast lt_of_lt_of_le zero_lt_one ha), ← mul_pow]
    congr 2
    rw [hr_def, Real.rpow_neg hb0.le, div_eq_mul_inv]
  have h1r : (0 : ℝ) < 1 - r := by linarith
  -- upper bound by induction, keeping track of the geometric partial sum
  have hup : ∀ k : ℕ, T k ≤ (a : ℝ) ^ k * (T₀ + C * ((r - r ^ (k + 1)) / (1 - r))) := by
    intro k
    induction k with
    | zero => simp [hTbase]
    | succ k ih =>
        have hstep : (a : ℝ) * T k ≤
            (a : ℝ) ^ (k + 1) * (T₀ + C * ((r - r ^ (k + 1)) / (1 - r))) := by
          calc (a : ℝ) * T k
              ≤ (a : ℝ) * ((a : ℝ) ^ k * (T₀ + C * ((r - r ^ (k + 1)) / (1 - r)))) := by
                exact mul_le_mul_of_nonneg_left ih ha0.le
            _ = (a : ℝ) ^ (k + 1) * (T₀ + C * ((r - r ^ (k + 1)) / (1 - r))) := by ring
        have hfb : f (k + 1) ≤ C * ((a : ℝ) ^ (k + 1) * r ^ (k + 1)) := hfk (k + 1)
        have key : (a : ℝ) ^ (k + 1) * (T₀ + C * ((r - r ^ (k + 1)) / (1 - r)))
            + C * ((a : ℝ) ^ (k + 1) * r ^ (k + 1))
            = (a : ℝ) ^ (k + 1) * (T₀ + C * ((r - r ^ (k + 2)) / (1 - r))) := by
          field_simp
          ring
        rw [hTrec k]
        calc (a : ℝ) * T k + f (k + 1)
            ≤ (a : ℝ) ^ (k + 1) * (T₀ + C * ((r - r ^ (k + 1)) / (1 - r)))
              + C * ((a : ℝ) ^ (k + 1) * r ^ (k + 1)) := by linarith
          _ = (a : ℝ) ^ (k + 1) * (T₀ + C * ((r - r ^ (k + 2)) / (1 - r))) := key
  -- lower bound by induction
  have hlow : ∀ k : ℕ, (a : ℝ) ^ k * T₀ ≤ T k := by
    intro k
    induction k with
    | zero => simp [hTbase]
    | succ k ih =>
        rw [hTrec k]
        have : (a : ℝ) ^ (k + 1) * T₀ ≤ (a : ℝ) * T k := by
          have := mul_le_mul_of_nonneg_left ih ha0.le
          calc (a : ℝ) ^ (k + 1) * T₀ = (a : ℝ) * ((a : ℝ) ^ k * T₀) := by ring
            _ ≤ (a : ℝ) * T k := this
        linarith [hf0 (k + 1)]
  refine ⟨T₀, T₀ + C * (r / (1 - r)), hT₀, ?_, ?_⟩
  · have : 0 < C * (r / (1 - r)) := by positivity
    linarith
  · intro k
    rw [hcrit k]
    constructor
    · rw [mul_comm]; exact hlow k
    · refine (hup k).trans ?_
      have hak : (0 : ℝ) < (a : ℝ) ^ k := pow_pos ha0 k
      have hmono : (r - r ^ (k + 1)) / (1 - r) ≤ r / (1 - r) := by
        have hsplit : (r - r ^ (k + 1)) / (1 - r) = r / (1 - r) - r ^ (k + 1) / (1 - r) :=
          sub_div _ _ _
        have hnn : 0 ≤ r ^ (k + 1) / (1 - r) := by positivity
        rw [hsplit]; linarith
      have : T₀ + C * ((r - r ^ (k + 1)) / (1 - r)) ≤ T₀ + C * (r / (1 - r)) := by
        have := mul_le_mul_of_nonneg_left hmono hC.le
        linarith
      calc (a : ℝ) ^ k * (T₀ + C * ((r - r ^ (k + 1)) / (1 - r)))
          ≤ (a : ℝ) ^ k * (T₀ + C * (r / (1 - r))) :=
            mul_le_mul_of_nonneg_left this hak.le
        _ = (T₀ + C * (r / (1 - r))) * (a : ℝ) ^ k := by ring

/-- **Master theorem, case 1.**

Let `T` satisfy the divide-and-conquer recurrence
`T n = a * T (n / b) + f n` for `n` a power of `b`, i.e.
`T (b ^ (k + 1)) = a * T (b ^ k) + f (b ^ (k + 1))`,
where there are `a ≥ 1` subproblems (`b ≥ 2`), the combine cost `f` is nonnegative,
the base value `T 1` is positive, and `f n = O (n ^ (log_b a - ε))` for some `ε > 0`.

Then `T n = Θ (n ^ (log_b a))` along the powers of `b`: there are positive constants
`c₁, c₂` such that for every `n = b ^ k`,
`c₁ * n ^ (log_b a) ≤ T n ≤ c₂ * n ^ (log_b a)`. -/
