/-
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to precede any module docstring, so the header above
-- is a plain comment and is repeated as the module docstring below.)
import Mathlib

/-!
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-
Remark: Mathlib has no Master-theorem lemma; `exact?`/`apply?` find nothing that
closes this goal.  The proof below is self-contained, using only standard `rpow`
lemmas (`Real.rpow_logb`, `Real.rpow_sub`, `Real.rpow_natCast`, `Real.rpow_mul`).
-/

/-- Auxiliary: for `0 ≤ x`, natural powers and real powers commute. -/
lemma pow_rpow_comm (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (s : ℝ) :
    (x ^ k) ^ s = (x ^ s) ^ k := by
  rw [← Real.rpow_natCast x k, ← Real.rpow_natCast (x ^ s) k, ← Real.rpow_mul hx,
    ← Real.rpow_mul hx, mul_comm]

/-- `(b^k)^(log_b a) = a^k`. -/
lemma rpow_logb_pow (a : ℝ) (b : ℕ) (hb : 2 ≤ b) (ha : 0 < a) (k : ℕ) :
    (((b : ℝ) ^ k) ^ Real.logb b a) = a ^ k := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb.trans_lt' (by norm_num)
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := by linarith
  rw [pow_rpow_comm _ hb0, Real.rpow_logb (by linarith) (by linarith) ha]

/--
**Master theorem, case 1** (on exact powers of `b`).

If `T (b^(k+1)) = a * T (b^k) + f (b^(k+1))` with `a ≥ 1`, `b ≥ 2`, `f ≥ 0` and
`f n ≤ C * n ^ (log_b a - ε)` for some `ε > 0`, then `T (b^k) = Θ ((b^k) ^ (log_b a))`:
there are positive constants `c₁, c₂` with
`c₁ * (b^k)^(log_b a) ≤ T (b^k) ≤ c₂ * (b^k)^(log_b a)` for all `k`.
-/
theorem master_theorem_case1
    (a : ℝ) (b : ℕ) (eps C : ℝ) (f T : ℕ → ℝ)
    (ha : 1 ≤ a) (hb : 2 ≤ b) (heps : 0 < eps) (hC : 0 ≤ C)
    (hT0 : 0 < T 1)
    (hrec : ∀ k : ℕ, T (b ^ (k + 1)) = a * T (b ^ k) + f (b ^ (k + 1)))
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (hf : ∀ n : ℕ, f n ≤ C * ((n : ℝ)) ^ (Real.logb b a - eps)) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ k : ℕ, c₁ * (((b : ℝ) ^ k) ^ Real.logb b a) ≤ T (b ^ k) ∧
               T (b ^ k) ≤ c₂ * (((b : ℝ) ^ k) ^ Real.logb b a) := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb.trans_lt' (by norm_num)
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := by linarith
  set r : ℝ := (b : ℝ) ^ (-eps) with hr_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by linarith) _
  have hr1 : r < 1 := by
    rw [hr_def]
    apply Real.rpow_lt_one_of_one_lt_of_neg hb1
    linarith
  have h1r : (1 : ℝ) - r ≠ 0 := by linarith
  have hrinv : r = ((b : ℝ) ^ eps)⁻¹ := by rw [hr_def, Real.rpow_neg hb0]
  -- pointwise bound on `f (b ^ k)`
  have hfb : ∀ k : ℕ, f (b ^ k) ≤ C * (a ^ k * r ^ k) := by
    intro k
    have h := hf (b ^ k)
    have hcast : ((b ^ k : ℕ) : ℝ) = ((b : ℝ)) ^ k := by push_cast; ring
    rw [hcast] at h
    have heq : (((b : ℝ) ^ k) ^ (Real.logb b a - eps)) = a ^ k * r ^ k := by
      rw [pow_rpow_comm _ hb0, Real.rpow_sub (by linarith),
        Real.rpow_logb (by linarith) (by linarith) ha0, hrinv, div_eq_mul_inv, mul_pow]
    rw [heq] at h
    exact h
  set D : ℝ := C * r / (1 - r) with hD_def
  have hD0 : 0 ≤ D := by
    apply div_nonneg (mul_nonneg hC hr0.le)
    linarith
  -- lower bound
  have hlow : ∀ k : ℕ, T 1 * a ^ k ≤ T (b ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hrec k
      have h1 : a * (T 1 * a ^ k) ≤ a * T (b ^ k) := by nlinarith
      have h2 : 0 ≤ f (b ^ (k + 1)) := hf_nonneg _
      rw [this]
      calc T 1 * a ^ (k + 1) = a * (T 1 * a ^ k) := by ring
        _ ≤ a * T (b ^ k) := h1
        _ ≤ a * T (b ^ k) + f (b ^ (k + 1)) := by linarith
  -- upper bound, strengthened induction
  have hup : ∀ k : ℕ, T (b ^ k) ≤ a ^ k * (T 1 + D * (1 - r ^ k)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hrk : (0:ℝ) < r ^ k := pow_pos hr0 k
      have hak : (0:ℝ) < a ^ k := pow_pos ha0 k
      have key : C * r ^ (k + 1) = D * (1 - r) * r ^ k := by
        rw [hD_def, div_mul_eq_mul_div, mul_div_assoc]
        rw [div_self h1r]
        ring
      have h1 : a * T (b ^ k) ≤ a * (a ^ k * (T 1 + D * (1 - r ^ k))) := by nlinarith
      have h2 : f (b ^ (k+1)) ≤ C * (a ^ (k+1) * r ^ (k+1)) := hfb (k+1)
      rw [hrec k]
      have expand : a ^ (k+1) * (T 1 + D * (1 - r ^ (k+1)))
          = a * (a ^ k * (T 1 + D * (1 - r ^ k))) + C * (a ^ (k+1) * r ^ (k+1)) := by
        have : C * (a ^ (k+1) * r ^ (k+1)) = a ^ (k+1) * (D * (1 - r) * r ^ k) := by
          rw [← key]; ring
        rw [this]
        ring
      linarith [h1, h2, expand]
  refine ⟨T 1, T 1 + D, hT0, by linarith, ?_⟩
  intro k
  have hpow : (((b : ℝ) ^ k) ^ Real.logb b a) = a ^ k := rpow_logb_pow a b hb ha0 k
  rw [hpow]
  refine ⟨by linarith [hlow k], ?_⟩
  have hrk : (0:ℝ) < r ^ k := pow_pos hr0 k
  have hak : (0:ℝ) < a ^ k := pow_pos ha0 k
  nlinarith [hup k, mul_nonneg hD0 hrk.le]

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

