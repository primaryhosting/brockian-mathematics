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

namespace CS

/-- `((b:ℝ)^k) ^ (log_b a) = a ^ k` (outer exponent is a real power). -/
lemma rpow_logb_pow {a b : ℝ} (ha : 0 < a) (hb : 1 < b) (k : ℕ) :
    ((b : ℝ) ^ k) ^ (Real.logb b a) = a ^ k := by
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb
  rw [← Real.rpow_natCast (b : ℝ) k, ← Real.rpow_mul hb0.le, mul_comm,
    Real.rpow_mul hb0.le, Real.rpow_logb hb0 (ne_of_gt hb) ha, Real.rpow_natCast]

/-- `((b:ℝ)^k) ^ (-ε) = ((b:ℝ) ^ (-ε)) ^ k`. -/
lemma rpow_neg_pow {b : ℝ} (hb : 1 < b) (e : ℝ) (k : ℕ) :
    ((b : ℝ) ^ k) ^ (-e) = ((b : ℝ) ^ (-e)) ^ k := by
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb
  rw [← Real.rpow_natCast (b : ℝ) k, ← Real.rpow_mul hb0.le, mul_comm,
    Real.rpow_mul hb0.le, Real.rpow_natCast]

section

variable {a e C : ℝ} {b : ℕ} {T f : ℕ → ℝ}

/-- Under the case-1 hypotheses, `f (b^k) ≤ C * a^k * r^k` where `r = b^(-ε)`. -/
lemma f_pow_bound (ha : 0 < a) (hb : 2 ≤ b)
    (hf : ∀ n : ℕ, 1 ≤ n → f n ≤ C * (n : ℝ) ^ (Real.logb b a - e)) (k : ℕ) :
    f (b ^ k) ≤ C * a ^ k * ((b : ℝ) ^ (-e)) ^ k := by
  have hb1 : (1 : ℝ) < (b : ℕ) := by exact_mod_cast hb.trans_lt' one_lt_two
  have hbk : 1 ≤ b ^ k := Nat.one_le_pow _ _ (by omega)
  have := hf (b ^ k) hbk
  have hcast : ((b ^ k : ℕ) : ℝ) = ((b : ℝ)) ^ k := by push_cast; ring
  rw [hcast] at this
  have hsplit : ((b : ℝ) ^ k) ^ (Real.logb b a - e)
      = a ^ k * ((b : ℝ) ^ (-e)) ^ k := by
    have hbk0 : (0 : ℝ) < (b : ℝ) ^ k := pow_pos (lt_trans zero_lt_one hb1) k
    rw [sub_eq_add_neg, Real.rpow_add hbk0, rpow_logb_pow ha hb1 k, rpow_neg_pow hb1 e k]
  rw [hsplit] at this
  linarith [this]

/-- Lower bound: `a^k * T 1 ≤ T (b^k)`. -/
lemma master_lower (ha : 0 < a) (hfnn : ∀ n : ℕ, 0 ≤ f n)
    (hrec : ∀ k : ℕ, T (b ^ (k + 1)) = a * T (b ^ k) + f (b ^ (k + 1))) (k : ℕ) :
    a ^ k * T 1 ≤ T (b ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h := hrec k
      have : a * (a ^ k * T 1) ≤ a * T (b ^ k) := by
        exact mul_le_mul_of_nonneg_left ih ha.le
      have hf := hfnn (b ^ (k + 1))
      calc a ^ (k + 1) * T 1 = a * (a ^ k * T 1) := by ring
        _ ≤ a * T (b ^ k) := this
        _ ≤ a * T (b ^ k) + f (b ^ (k + 1)) := by linarith
        _ = T (b ^ (k + 1)) := h.symm

/-- Strengthened upper bound used for the induction. -/
lemma master_upper_aux (ha : 0 < a) (hb : 2 ≤ b) (he : 0 < e) (hC : 0 ≤ C)
    (hf : ∀ n : ℕ, 1 ≤ n → f n ≤ C * (n : ℝ) ^ (Real.logb b a - e))
    (hrec : ∀ k : ℕ, T (b ^ (k + 1)) = a * T (b ^ k) + f (b ^ (k + 1))) (k : ℕ) :
    T (b ^ k) ≤ (T 1 + (C * ((b : ℝ) ^ (-e)) / (1 - (b : ℝ) ^ (-e)))
      * (1 - ((b : ℝ) ^ (-e)) ^ k)) * a ^ k := by
  have hb1 : (1 : ℝ) < (b : ℕ) := by exact_mod_cast hb.trans_lt' one_lt_two
  set r : ℝ := (b : ℝ) ^ (-e) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (lt_trans zero_lt_one hb1) _
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one_of_one_lt_of_neg hb1 (by linarith)
  set D : ℝ := C * r / (1 - r) with hD
  have hDnn : 0 ≤ D := by
    apply div_nonneg (mul_nonneg hC hr0.le)
    linarith
  have h1r : (1 : ℝ) - r ≠ 0 := by linarith
  have hDeq : D * (1 - r) = C * r := by
    rw [hD, div_mul_cancel₀ _ h1r]
  induction k with
  | zero => simp
  | succ k ih =>
      have hfb : f (b ^ (k + 1)) ≤ C * a ^ (k + 1) * r ^ (k + 1) :=
        f_pow_bound ha hb hf (k + 1)
      have hstep : T (b ^ (k + 1)) = a * T (b ^ k) + f (b ^ (k + 1)) := hrec k
      have hmul : a * T (b ^ k) ≤ a * ((T 1 + D * (1 - r ^ k)) * a ^ k) :=
        mul_le_mul_of_nonneg_left ih ha.le
      have hak : (0 : ℝ) < a ^ (k + 1) := pow_pos ha _
      have key : (T 1 + D * (1 - r ^ k)) * a ^ (k + 1) + C * a ^ (k + 1) * r ^ (k + 1)
          ≤ (T 1 + D * (1 - r ^ (k + 1))) * a ^ (k + 1) := by
        have : C * r ^ (k + 1) ≤ D * (1 - r ^ (k+1)) - D * (1 - r ^ k) := by
          have h2 : D * (1 - r ^ (k+1)) - D * (1 - r ^ k) = D * (1 - r) * r ^ k := by
            ring
          rw [h2, hDeq]
          exact le_of_eq (by ring)
        nlinarith [hak, this]
      calc T (b ^ (k + 1)) = a * T (b ^ k) + f (b ^ (k + 1)) := hstep
        _ ≤ a * ((T 1 + D * (1 - r ^ k)) * a ^ k) + C * a ^ (k + 1) * r ^ (k + 1) := by
              linarith
        _ = (T 1 + D * (1 - r ^ k)) * a ^ (k + 1) + C * a ^ (k + 1) * r ^ (k + 1) := by ring
        _ ≤ (T 1 + D * (1 - r ^ (k + 1))) * a ^ (k + 1) := key

end

/--
**Master theorem, case 1.**

Let `T` satisfy the divide-and-conquer recurrence `T(n) = a·T(n/b) + f(n)` on the exact
powers of `b` (i.e. `T (b^(k+1)) = a · T (b^k) + f (b^(k+1))`), with `a > 0`, `b ≥ 2`,
`f ≥ 0` and `T 1 > 0`.  If `f(n) = O(n^{log_b a − ε})` for some `ε > 0` — here witnessed
explicitly by the bound `f n ≤ C · n^{log_b a − ε}` for all `n ≥ 1` — then
`T(n) = Θ(n^{log_b a})`, i.e. there are positive constants `c₁, c₂` with
`c₁ · n^{log_b a} ≤ T(n) ≤ c₂ · n^{log_b a}` for all `n = b^k`.
-/
theorem master_theorem_case1
    {a e C : ℝ} {b : ℕ} {T f : ℕ → ℝ}
    (ha : 0 < a) (hb : 2 ≤ b) (he : 0 < e) (hC : 0 ≤ C)
    (hT1 : 0 < T 1)
    (hfnn : ∀ n : ℕ, 0 ≤ f n)
    (hf : ∀ n : ℕ, 1 ≤ n → f n ≤ C * (n : ℝ) ^ (Real.logb b a - e))
    (hrec : ∀ k : ℕ, T (b ^ (k + 1)) = a * T (b ^ k) + f (b ^ (k + 1))) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ,
      c₁ * ((b : ℝ) ^ k) ^ (Real.logb b a) ≤ T (b ^ k) ∧
        T (b ^ k) ≤ c₂ * ((b : ℝ) ^ k) ^ (Real.logb b a) := by
  have hb1 : (1 : ℝ) < (b : ℕ) := by exact_mod_cast hb.trans_lt' one_lt_two
  set r : ℝ := (b : ℝ) ^ (-e) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (lt_trans zero_lt_one hb1) _
  have hr1 : r < 1 := by
    rw [hr]; exact Real.rpow_lt_one_of_one_lt_of_neg hb1 (by linarith)
  set D : ℝ := C * r / (1 - r) with hD
  have hDnn : 0 ≤ D := by
    apply div_nonneg (mul_nonneg hC hr0.le); linarith
  refine ⟨T 1, T 1 + D, hT1, by linarith, fun k => ?_⟩
  have hpow : ((b : ℝ) ^ k) ^ (Real.logb b a) = a ^ k := rpow_logb_pow ha hb1 k
  rw [hpow]
  constructor
  · have := master_lower ha hfnn hrec k
    linarith [this]
  · have hup := master_upper_aux ha hb he hC hf hrec k
    have hak : (0 : ℝ) < a ^ k := pow_pos ha _
    have hrk : 0 < r ^ k := pow_pos hr0 k
    have hrk1 : r ^ k ≤ 1 := pow_le_one₀ hr0.le hr1.le
    have : (T 1 + D * (1 - r ^ k)) * a ^ k ≤ (T 1 + D) * a ^ k := by
      have : D * (1 - r ^ k) ≤ D := by nlinarith
      nlinarith
    linarith

end CS

