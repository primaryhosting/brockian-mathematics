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

Case 1 of the Master Theorem for divide-and-conquer recurrences:
if `T(n) = a * T(n/b) + f(n)` with `f(n) = O(n^(log_b a - ε))` for some `ε > 0`,
then `T(n) = Θ(n^(log_b a))`.

As usual for the Master Theorem, the recurrence is analysed along the powers of `b`,
i.e. we write `T k` for the value of the recurrence at `n = b ^ k`.
-/

namespace CS

/-- At `n = b ^ k`, the driving function `n ^ (log_b a)` equals `a ^ k`. -/
theorem rpow_logb_pow (a b : ℝ) (ha : 0 < a) (hb : 1 < b) (k : ℕ) :
    ((b : ℝ) ^ k) ^ Real.logb b a = a ^ k := by
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb
  rw [← Real.rpow_natCast b k, ← Real.rpow_mul hb0.le, mul_comm,
    Real.rpow_mul hb0.le, Real.rpow_logb hb0 (ne_of_gt hb) ha, Real.rpow_natCast]

/-- At `n = b ^ k`, we have `n ^ (log_b a - ε) = a ^ k / (b ^ ε) ^ k`. -/
theorem rpow_logb_sub_pow (a b ε : ℝ) (ha : 0 < a) (hb : 1 < b) (k : ℕ) :
    ((b : ℝ) ^ k) ^ (Real.logb b a - ε) = a ^ k / ((b : ℝ) ^ ε) ^ k := by
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb
  have hbk : (0 : ℝ) < (b : ℝ) ^ k := pow_pos hb0 k
  rw [Real.rpow_sub hbk, rpow_logb_pow a b ha hb k]
  congr 1
  rw [← Real.rpow_natCast b k, ← Real.rpow_mul hb0.le, mul_comm,
    Real.rpow_mul hb0.le, Real.rpow_natCast]

/-- **Master Theorem, Case 1.**  Consider a divide-and-conquer recurrence
`T(n) = a * T(n / b) + f(n)` with `a ≥ 1`, `b > 1`, driving function `f ≥ 0`
satisfying `f(x) ≤ C * x ^ (log_b a - ε)` for some `ε > 0` (i.e. `f(n) = O(n^(log_b a - ε))`).
Then `T(n) = Θ(n ^ (log_b a))`: there are positive constants `c₁, c₂` with
`c₁ * n ^ (log_b a) ≤ T(n) ≤ c₂ * n ^ (log_b a)` for all `n = b ^ k`.
Here `T k` denotes the value of the recurrence at `n = b ^ k`. -/
theorem master_theorem_case1
    (a b ε C : ℝ) (ha : 1 ≤ a) (hb : 1 < b) (hε : 0 < ε) (hC : 0 ≤ C)
    (f : ℝ → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hf : ∀ x, 1 ≤ x → f x ≤ C * x ^ (Real.logb b a - ε))
    (T : ℕ → ℝ) (hT0 : 0 < T 0)
    (hTrec : ∀ k, T (k + 1) = a * T k + f ((b : ℝ) ^ (k + 1))) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ,
      c₁ * ((b : ℝ) ^ k) ^ Real.logb b a ≤ T k ∧
        T k ≤ c₂ * ((b : ℝ) ^ k) ^ Real.logb b a := by
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  set d : ℝ := (b : ℝ) ^ ε with hd_def
  have hd1 : 1 < d := Real.one_lt_rpow_iff_of_pos hb0 |>.2 (Or.inl ⟨hb, hε⟩)
  have hd0 : (0 : ℝ) < d := lt_trans zero_lt_one hd1
  set K : ℝ := C / (d - 1) with hK_def
  have hK0 : 0 ≤ K := div_nonneg hC (by linarith)
  -- bound on the driving function along powers of `b`
  have hfbound : ∀ k : ℕ, f ((b : ℝ) ^ (k + 1)) ≤ C * (a ^ (k + 1) / d ^ (k + 1)) := by
    intro k
    have h1 : (1 : ℝ) ≤ (b : ℝ) ^ (k + 1) := one_le_pow₀ hb.le
    calc f ((b : ℝ) ^ (k + 1)) ≤ C * ((b : ℝ) ^ (k + 1)) ^ (Real.logb b a - ε) := hf _ h1
      _ = C * (a ^ (k + 1) / d ^ (k + 1)) := by
          rw [rpow_logb_sub_pow a b ε ha0 hb]
  -- lower bound
  have hlow : ∀ k : ℕ, T 0 * a ^ k ≤ T k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h1 : a * (T 0 * a ^ k) ≤ a * T k := by nlinarith
        have h2 := hf0 ((b : ℝ) ^ (k + 1))
        calc T 0 * a ^ (k + 1) = a * (T 0 * a ^ k) := by ring
          _ ≤ a * T k := h1
          _ ≤ a * T k + f ((b : ℝ) ^ (k + 1)) := by linarith
          _ = T (k + 1) := (hTrec k).symm
  -- upper bound (sharp form, by induction)
  have hup : ∀ k : ℕ, T k ≤ (T 0 + K) * a ^ k - K * (a ^ k / d ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hdk : (0 : ℝ) < d ^ k := pow_pos hd0 k
        have hak : (0 : ℝ) < a ^ k := pow_pos ha0 k
        have hstep := hfbound k
        have hne : d - 1 ≠ 0 := by intro h; nlinarith
        have hKd : K * (d - 1) = C := by
          rw [hK_def]; field_simp
        rw [hTrec k]
        have h1 : a * T k ≤ a * ((T 0 + K) * a ^ k - K * (a ^ k / d ^ k)) := by
          nlinarith
        have key : a * ((T 0 + K) * a ^ k - K * (a ^ k / d ^ k))
            + C * (a ^ (k + 1) / d ^ (k + 1))
            = (T 0 + K) * a ^ (k + 1) - K * (a ^ (k + 1) / d ^ (k + 1)) := by
          rw [← hKd]
          field_simp
          ring
        linarith
  refine ⟨T 0, T 0 + K, hT0, by linarith, ?_⟩
  intro k
  rw [rpow_logb_pow a b ha0 hb]
  refine ⟨hlow k, ?_⟩
  have hdk : (0 : ℝ) < d ^ k := pow_pos hd0 k
  have hak : (0 : ℝ) < a ^ k := pow_pos ha0 k
  have : 0 ≤ K * (a ^ k / d ^ k) := by positivity
  linarith [hup k]

/-- The same conclusion phrased with Mathlib's asymptotic `Θ` notation:
along `n = b ^ k` the solution of the recurrence is `Θ(n ^ (log_b a))`. -/
theorem master_theorem_case1_isTheta
    (a b ε C : ℝ) (ha : 1 ≤ a) (hb : 1 < b) (hε : 0 < ε) (hC : 0 ≤ C)
    (f : ℝ → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hf : ∀ x, 1 ≤ x → f x ≤ C * x ^ (Real.logb b a - ε))
    (T : ℕ → ℝ) (hT0 : 0 < T 0)
    (hTrec : ∀ k, T (k + 1) = a * T k + f ((b : ℝ) ^ (k + 1))) :
    (fun k : ℕ => T k) =Θ[Filter.atTop]
      (fun k : ℕ => ((b : ℝ) ^ k) ^ Real.logb b a) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hbounds⟩ :=
    master_theorem_case1 a b ε C ha hb hε hC f hf0 hf T hT0 hTrec
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb
  have hgpos : ∀ k : ℕ, (0 : ℝ) < ((b : ℝ) ^ k) ^ Real.logb b a := fun k =>
    Real.rpow_pos_of_pos (pow_pos hb0 k) _
  have hTpos : ∀ k : ℕ, (0 : ℝ) < T k := fun k =>
    lt_of_lt_of_le (mul_pos hc₁ (hgpos k)) (hbounds k).1
  constructor
  · refine Asymptotics.IsBigO.of_bound c₂ (Filter.Eventually.of_forall fun k => ?_)
    rw [Real.norm_of_nonneg (hTpos k).le, Real.norm_of_nonneg (hgpos k).le]
    exact (hbounds k).2
  · refine Asymptotics.IsBigO.of_bound c₁⁻¹ (Filter.Eventually.of_forall fun k => ?_)
    rw [Real.norm_of_nonneg (hTpos k).le, Real.norm_of_nonneg (hgpos k).le]
    rw [inv_mul_eq_div, le_div_iff₀ hc₁, mul_comm]
    exact (hbounds k).1

/-- Sanity check: `T(n) = 2 * T(n/2) + 1` with `T(1) = 1` is `Θ(n)`
(here `log_2 2 = 1`, and the driving function `f ≡ 1` is `O(n ^ (1 - 1/2))`). -/
example (T : ℕ → ℝ) (hT0 : T 0 = 1) (hTrec : ∀ k, T (k + 1) = 2 * T k + 1) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ,
      c₁ * ((2 : ℝ) ^ k) ^ Real.logb 2 2 ≤ T k ∧
        T k ≤ c₂ * ((2 : ℝ) ^ k) ^ Real.logb 2 2 := by
  refine master_theorem_case1 2 2 (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (fun _ => 1) (fun _ => zero_le_one) (fun x hx => ?_) T (by rw [hT0]; norm_num)
    (by simpa using hTrec)
  have h : Real.logb 2 2 - 1 / 2 = 1 / 2 := by
    rw [show Real.logb 2 2 = 1 from Real.logb_self_eq_one (by norm_num)]
    norm_num
  simp only [h, one_mul]
  calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 2) := by norm_num
    _ ≤ x ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow zero_le_one hx (by norm_num)

end CS

import Mathlib

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

