import Mathlib

/-!
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-- Commuting a natural power with a real power: `(b ^ k) ^ c = (b ^ c) ^ k`. -/
lemma pow_rpow_comm {b : ℝ} (hb : 0 ≤ b) (c : ℝ) (k : ℕ) :
    ((b ^ k : ℝ)) ^ c = ((b : ℝ) ^ c) ^ k := by
  rw [← Real.rpow_natCast b k, ← Real.rpow_mul hb, mul_comm, Real.rpow_mul hb,
    Real.rpow_natCast]

/-- On the points `n = b ^ k`, the function `n ↦ n ^ (log_b a)` is `a ^ k`. -/
lemma rpow_logb_pow {a b : ℝ} (ha : 0 < a) (hb : 1 < b) (k : ℕ) :
    ((b ^ k : ℝ)) ^ (Real.logb b a) = a ^ k := by
  have hb0 : (0 : ℝ) < b := lt_trans one_pos hb
  rw [pow_rpow_comm hb0.le, Real.rpow_logb hb0 hb.ne' ha]

/-- On the points `n = b ^ k`, the function `n ↦ n ^ (log_b a - ε)` equals
`a ^ k * r ^ k` where `r = b ^ (-ε) < 1`. -/
lemma rpow_logb_sub_pow {a b eps : ℝ} (ha : 0 < a) (hb : 1 < b) (k : ℕ) :
    ((b ^ k : ℝ)) ^ (Real.logb b a - eps) = a ^ k * ((b : ℝ) ^ (-eps)) ^ k := by
  have hb0 : (0 : ℝ) < b := lt_trans one_pos hb
  rw [pow_rpow_comm hb0.le, ← mul_pow]
  congr 1
  rw [sub_eq_add_neg, Real.rpow_add hb0, Real.rpow_logb hb0 hb.ne' ha]

/-- **Master theorem, Case 1** (on the exact powers of `b`).

Let `T` satisfy the divide-and-conquer recurrence `T(n) = a·T(n/b) + f(n)`, written here
along the powers of `b`: `T k` stands for `T (b ^ k)` and `f k` for `f (b ^ k)`, so the
recurrence reads `T (k+1) = a * T k + f (k+1)`.

Assume `a ≥ 1`, `b > 1`, the driving function `f` is nonnegative and satisfies the
`O(n ^ (log_b a - ε))` bound `f (b ^ k) ≤ C * (b ^ k) ^ (log_b a - ε)` with `ε > 0`, and
`T (b ^ 0) > 0`.

Then `T (b ^ k) = Θ((b ^ k) ^ (log_b a))`: there are positive constants `c₁, c₂` with
`c₁ * n ^ (log_b a) ≤ T n ≤ c₂ * n ^ (log_b a)` for all `n = b ^ k`. -/
theorem master_theorem_case1
    {a b eps C : ℝ} {f T : ℕ → ℝ}
    (ha : 1 ≤ a) (hb : 1 < b) (heps : 0 < eps) (hC : 0 < C)
    (hf0 : ∀ k, 0 ≤ f k)
    (hfO : ∀ k, f k ≤ C * ((b ^ k : ℝ)) ^ (Real.logb b a - eps))
    (hT0 : 0 < T 0)
    (hrec : ∀ k, T (k + 1) = a * T k + f (k + 1)) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ,
      c₁ * ((b ^ k : ℝ)) ^ (Real.logb b a) ≤ T k ∧
        T k ≤ c₂ * ((b ^ k : ℝ)) ^ (Real.logb b a) := by
  have hb0 : (0 : ℝ) < b := lt_trans one_pos hb
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha
  set r : ℝ := (b : ℝ) ^ (-eps) with hr_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos hb0 _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb (neg_neg_iff_pos.mpr heps)
  set D : ℝ := C * r / (1 - r) with hD_def
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  have hD0 : 0 < D := div_pos (mul_pos hC hr0) h1r
  have h1rne : (1 - r) ≠ 0 := ne_of_gt h1r
  have hDkey : C * r + D * r = D := by
    rw [hD_def]
    field_simp
    ring
  set M : ℝ := T 0 + D with hM_def
  -- Lower bound
  have hlow : ∀ k : ℕ, T 0 * a ^ k ≤ T k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hfk : 0 ≤ f (k + 1) := hf0 _
        have hmul : a * (T 0 * a ^ k) ≤ a * T k := mul_le_mul_of_nonneg_left ih ha0.le
        have hpk : T 0 * a ^ (k + 1) = a * (T 0 * a ^ k) := by ring
        rw [hrec k]
        linarith
  -- Upper bound, with a strengthened induction hypothesis
  have hup : ∀ k : ℕ, T k ≤ a ^ k * (M - D * r ^ k) := by
    intro k
    induction k with
    | zero => simp [hM_def]
    | succ k ih =>
        have hfk : f (k + 1) ≤ C * (a ^ (k + 1) * r ^ (k + 1)) := by
          have := hfO (k + 1)
          rwa [rpow_logb_sub_pow ha0 hb (k + 1)] at this
        have hmul : a * T k ≤ a * (a ^ k * (M - D * r ^ k)) :=
          mul_le_mul_of_nonneg_left ih ha0.le
        have hak : (0 : ℝ) < a ^ k := pow_pos ha0 k
        have hrk : (0 : ℝ) < r ^ k := pow_pos hr0 k
        rw [hrec k]
        have hzero : D - (C * r + D * r) = 0 := by rw [hDkey]; ring
        have hstep : a * (a ^ k * (M - D * r ^ k)) + C * (a ^ (k + 1) * r ^ (k + 1))
            ≤ a ^ (k + 1) * (M - D * r ^ (k + 1)) := by
          have hid : a ^ (k + 1) * (M - D * r ^ (k + 1))
              - (a * (a ^ k * (M - D * r ^ k)) + C * (a ^ (k + 1) * r ^ (k + 1)))
              = a * a ^ k * r ^ k * (D - (C * r + D * r)) := by ring
          rw [hzero, mul_zero] at hid
          linarith
        linarith
  refine ⟨T 0, M, hT0, by positivity, fun k => ?_⟩
  have hpow : ((b ^ k : ℝ)) ^ (Real.logb b a) = a ^ k := rpow_logb_pow ha0 hb k
  refine ⟨?_, ?_⟩
  · rw [hpow]; exact hlow k
  · rw [hpow]
    have hak : (0 : ℝ) < a ^ k := pow_pos ha0 k
    have hnn : (0 : ℝ) ≤ a ^ k * (D * r ^ k) :=
      le_of_lt (mul_pos hak (mul_pos hD0 (pow_pos hr0 k)))
    have hid : a ^ k * (M - D * r ^ k) = M * a ^ k - a ^ k * (D * r ^ k) := by ring
    linarith [hup k]

end CS

