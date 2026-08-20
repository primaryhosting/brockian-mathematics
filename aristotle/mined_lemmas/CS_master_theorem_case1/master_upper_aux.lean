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
