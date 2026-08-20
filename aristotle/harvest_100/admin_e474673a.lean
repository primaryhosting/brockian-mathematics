/-
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

open Real

/-- `((b:ℝ)^k) ^ t = (b ^ t) ^ k` for `b > 0`, natural `k`, real exponent `t`. -/
lemma rpow_pow_comm (b : ℝ) (hb : 0 < b) (t : ℝ) (k : ℕ) :
    ((b ^ k : ℝ)) ^ t = ((b : ℝ) ^ t) ^ k := by
  rw [← Real.rpow_natCast b k, ← Real.rpow_natCast (b ^ t) k, ← Real.rpow_mul hb.le,
    ← Real.rpow_mul hb.le, mul_comm]

/-- `(b^k)^(log_b a) = a^k`. -/
lemma pow_rpow_logb (a b : ℝ) (ha : 0 < a) (hb : 1 < b) (k : ℕ) :
    ((b ^ k : ℝ)) ^ (Real.logb b a) = a ^ k := by
  rw [rpow_pow_comm b (lt_trans zero_lt_one hb) _ k,
    Real.rpow_logb (lt_trans zero_lt_one hb) (ne_of_gt hb) ha]

/-- `(b^k)^(log_b a - ε) = a^k * (b^(-ε))^k`. -/
lemma pow_rpow_logb_sub (a b : ℝ) (ha : 0 < a) (hb : 1 < b) (e : ℝ) (k : ℕ) :
    ((b ^ k : ℝ)) ^ (Real.logb b a - e) = a ^ k * ((b : ℝ) ^ (-e)) ^ k := by
  have hb0 : (0:ℝ) < b := lt_trans zero_lt_one hb
  rw [rpow_pow_comm b hb0 _ k, ← mul_pow]
  congr 1
  rw [show Real.logb b a - e = Real.logb b a + (-e) by ring, Real.rpow_add hb0,
    Real.rpow_logb hb0 (ne_of_gt hb) ha]

/-- **Master theorem, case 1.**

Let `T` satisfy the divide-and-conquer recurrence `T n = a * T (n / b) + f n`, stated on the
powers of `b` (the standard domain on which the master theorem is proved):
`T (b^(k+1)) = a * T (b^k) + f (b^(k+1))`.  Assume `f` is nonnegative and
`f n = O (n ^ (log_b a - ε))` for some `ε > 0`, in the explicit form `f n ≤ C * n ^ (log_b a - ε)`.
Then `T (b^k) = Θ ((b^k) ^ (log_b a))`: there are positive constants `c₁, c₂` with
`c₁ * (b^k)^(log_b a) ≤ T (b^k) ≤ c₂ * (b^k)^(log_b a)` for all `k`.

Mathlib has no master theorem as such; the nearest existing machinery is the Akra–Bazzi theorem
(`Mathlib/Computability/AkraBazzi/AkraBazzi.lean`, `AkraBazziRecurrence`), which is stated for a
different (floor/ceiling based, smoothness-constrained) setup and does not close this statement.
The proof below is the standard geometric-series estimate on the recursion tree; the only
nontrivial library input is `Real.rpow_logb` (`b ^ logb b a = a`). -/
theorem master_theorem_case1
    (a : ℝ) (b : ℕ) (ha : 0 < a) (hb : 2 ≤ b)
    (e : ℝ) (he : 0 < e)
    (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n)
    (C : ℝ) (hC : 0 < C)
    (hfO : ∀ n, 1 ≤ n → f n ≤ C * (n : ℝ) ^ (Real.logb b a - e))
    (T : ℕ → ℝ) (hT1 : 0 < T 1)
    (hrec : ∀ k : ℕ, T (b ^ (k + 1)) = a * T (b ^ k) + f (b ^ (k + 1))) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ,
      c₁ * ((b : ℝ) ^ k) ^ (Real.logb b a) ≤ T (b ^ k) ∧
      T (b ^ k) ≤ c₂ * ((b : ℝ) ^ k) ^ (Real.logb b a) := by
  have hb1 : (1:ℝ) < (b : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hb
  have hb0 : (0:ℝ) < (b : ℝ) := lt_trans zero_lt_one hb1
  set r : ℝ := (b : ℝ) ^ (-e) with hr_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos hb0 _
  have hr1 : r < 1 := by
    rw [hr_def]
    exact Real.rpow_lt_one_of_one_lt_of_neg hb1 (by linarith)
  -- the hypothesis on `f`, specialised to the powers of `b`
  have hfb : ∀ k : ℕ, f (b ^ k) ≤ C * (a ^ k * r ^ k) := by
    intro k
    have h1 : 1 ≤ b ^ k := Nat.one_le_pow _ _ (by omega)
    have hcast : ((b ^ k : ℕ) : ℝ) = ((b : ℝ) ^ k) := by push_cast; ring
    have h := hfO (b ^ k) h1
    rw [hcast, pow_rpow_logb_sub a (b : ℝ) ha hb1 e k] at h
    exact h
  -- the constant coming from the geometric series
  obtain ⟨K, hK_def⟩ : ∃ K : ℝ, K = C * r / (1 - r) := ⟨_, rfl⟩
  have h1r : (0:ℝ) < 1 - r := by linarith
  have hK0 : 0 < K := by rw [hK_def]; exact div_pos (mul_pos hC hr0) h1r
  have hKeq : r * (K + C) = K := by
    rw [hK_def]; field_simp; ring
  refine ⟨T 1, T 1 + K, hT1, by linarith, ?_⟩
  -- lower bound: `T (b^k) ≥ T 1 * a^k`
  have hlow : ∀ k : ℕ, T 1 * a ^ k ≤ T (b ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hmul : a * (T 1 * a ^ k) ≤ a * T (b ^ k) := mul_le_mul_of_nonneg_left ih ha.le
      have hpow : T 1 * a ^ (k + 1) = a * (T 1 * a ^ k) := by ring
      have h2 : 0 ≤ f (b ^ (k + 1)) := hf0 _
      rw [hrec k, hpow]
      linarith
  -- upper bound, in a strengthened form suitable for induction
  have hup : ∀ k : ℕ, T (b ^ k) ≤ (T 1 + K) * a ^ k - K * (a * r) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hmul : a * T (b ^ k) ≤ a * ((T 1 + K) * a ^ k - K * (a * r) ^ k) :=
        mul_le_mul_of_nonneg_left ih ha.le
      have hstep : f (b ^ (k + 1)) ≤ C * (a ^ (k + 1) * r ^ (k + 1)) := hfb (k + 1)
      have hzero : r * (K + C) - K = 0 := by rw [hKeq]; ring
      have heq : a * ((T 1 + K) * a ^ k - K * (a * r) ^ k) + C * (a ^ (k + 1) * r ^ (k + 1))
          = (T 1 + K) * a ^ (k + 1) - K * (a * r) ^ (k + 1)
            + (a * (a ^ k * r ^ k)) * (r * (K + C) - K) := by
        rw [mul_pow, mul_pow]; ring
      rw [hzero, mul_zero, add_zero] at heq
      rw [hrec k]
      linarith
  intro k
  refine ⟨?_, ?_⟩
  · rw [pow_rpow_logb a (b : ℝ) ha hb1 k]
    exact hlow k
  · rw [pow_rpow_logb a (b : ℝ) ha hb1 k]
    have h2 : 0 ≤ K * (a * r) ^ k :=
      mul_nonneg hK0.le (pow_nonneg (mul_nonneg ha.le hr0.le) k)
    have := hup k
    linarith

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

