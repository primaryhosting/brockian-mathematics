import Mathlib

/-!
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to be the very first commands of a
module, so the header module docstring above is placed immediately after the import.
-/

namespace CS

open Real

section

variable {a b C ε : ℝ} {T f : ℕ → ℝ}

/-- On exact powers of `b`, `(b^k)^(log_b a) = a^k`. -/
lemma rpow_logb_pow (ha : 0 < a) (hb : 1 < b) (k : ℕ) :
    (b ^ (k : ℝ)) ^ (Real.logb b a) = a ^ k := by
  have hb0 : (0:ℝ) < b := lt_trans zero_lt_one hb
  rw [← Real.rpow_natCast a k, ← Real.rpow_mul hb0.le, mul_comm, Real.rpow_mul hb0.le,
    Real.rpow_logb hb0 (ne_of_gt hb) ha]

/-- On exact powers of `b`, `(b^k)^(log_b a - ε) = a^k * (b^(-ε))^k`. -/
lemma rpow_logb_sub_pow (ha : 0 < a) (hb : 1 < b) (k : ℕ) :
    (b ^ (k : ℝ)) ^ (Real.logb b a - ε) = a ^ k * (b ^ (-ε)) ^ k := by
  have hb0 : (0:ℝ) < b := lt_trans zero_lt_one hb
  have h1 : (b ^ (k : ℝ)) ^ (Real.logb b a - ε)
      = (b ^ (k:ℝ)) ^ (Real.logb b a) * (b ^ (k:ℝ)) ^ (-ε) := by
    rw [Real.rpow_sub (Real.rpow_pos_of_pos hb0 _)]
    rw [Real.rpow_neg (Real.rpow_pos_of_pos hb0 _).le]
    ring
  rw [h1, rpow_logb_pow ha hb k]
  congr 1
  rw [← Real.rpow_natCast (b ^ (-ε)) k, ← Real.rpow_mul hb0.le, ← Real.rpow_mul hb0.le]
  ring_nf

/-- Lower bound: with nonnegative driving term `f`, the recurrence satisfies
`a^k * T 0 ≤ T k`. -/
lemma master_lower (ha : 0 < a)
    (hrec : ∀ k, T (k + 1) = a * T k + f (k + 1))
    (hfnn : ∀ k, 0 ≤ f k) (k : ℕ) : a ^ k * T 0 ≤ T k := by
  induction k with
  | zero => simp
  | succ n ih =>
      have := hfnn (n + 1)
      rw [hrec n, pow_succ]
      nlinarith [ih, ha]

/-- Upper bound with the geometric-sum invariant. -/
lemma master_upper_aux (ha : 0 < a) (hb : 1 < b) (hC : 0 ≤ C) (hε : 0 < ε)
    (hrec : ∀ k, T (k + 1) = a * T k + f (k + 1))
    (hfO : ∀ k, f k ≤ C * (b ^ (k : ℝ)) ^ (Real.logb b a - ε)) (k : ℕ) :
    T k ≤ a ^ k * (T 0 + C / (1 - b ^ (-ε)) * (1 - (b ^ (-ε)) ^ k)) := by
  have hb0 : (0:ℝ) < b := lt_trans zero_lt_one hb
  set d : ℝ := b ^ (-ε) with hd
  have hd0 : 0 < d := Real.rpow_pos_of_pos hb0 _
  have hd1 : d < 1 := by
    rw [hd]
    apply Real.rpow_lt_one_of_one_lt_of_neg hb
    linarith
  set B : ℝ := C / (1 - d) with hB
  have hB0 : 0 ≤ B := div_nonneg hC (by linarith)
  have hkey : C * d ≤ B * (1 - d) := by
    rw [hB, div_mul_cancel₀]
    · nlinarith
    · linarith
  induction k with
  | zero => simp
  | succ n ih =>
      have hfb : f (n + 1) ≤ C * (a ^ (n+1) * d ^ (n+1)) := by
        have := hfO (n + 1)
        rwa [rpow_logb_sub_pow ha hb (n+1)] at this
      have hdn : 0 < d ^ n := pow_pos hd0 n
      have han : (0:ℝ) < a ^ (n+1) := pow_pos ha _
      have h2 : a * (a ^ n * (T 0 + B * (1 - d ^ n))) + f (n+1)
          ≤ a ^ (n+1) * (T 0 + B * (1 - d ^ (n+1))) := by
        have hstep : C * d ^ (n+1) ≤ B * d ^ n - B * d ^ (n+1) := by
          have : (C * d) * d ^ n ≤ (B * (1 - d)) * d ^ n :=
            mul_le_mul_of_nonneg_right hkey hdn.le
          calc C * d ^ (n+1) = (C * d) * d ^ n := by ring
            _ ≤ (B * (1 - d)) * d ^ n := this
            _ = B * d ^ n - B * d ^ (n+1) := by ring
        have := mul_le_mul_of_nonneg_left hstep han.le
        calc a * (a ^ n * (T 0 + B * (1 - d ^ n))) + f (n+1)
            ≤ a * (a ^ n * (T 0 + B * (1 - d ^ n))) + C * (a ^ (n+1) * d ^ (n+1)) := by
              linarith [hfb]
          _ = a ^ (n+1) * (T 0 + B * (1 - d ^ n)) + a ^ (n+1) * (C * d ^ (n+1)) := by
              ring
          _ ≤ a ^ (n+1) * (T 0 + B * (1 - d ^ n)) + a ^ (n+1) * (B * d ^ n - B * d ^ (n+1)) := by
              linarith [this]
          _ = a ^ (n+1) * (T 0 + B * (1 - d ^ (n+1))) := by ring
      have h3 : a * T n ≤ a * (a ^ n * (T 0 + B * (1 - d ^ n))) :=
        mul_le_mul_of_nonneg_left ih ha.le
      rw [hrec n]
      linarith

end

/-- **Master theorem, case 1** (on exact powers of `b`).

Let `T` satisfy the divide-and-conquer recurrence `T(b^(k+1)) = a * T(b^k) + f(b^(k+1))`
with `a > 0`, `b > 1`, `T(1) > 0`, and a nonnegative driving term `f` satisfying
`f(n) ≤ C * n^(log_b a - ε)` for some `ε > 0` (i.e. `f(n) = O(n^(log_b a - ε))`).
Then `T(n) = Θ(n^(log_b a))`: there are positive constants `c₁, c₂` with
`c₁ * n^(log_b a) ≤ T(n) ≤ c₂ * n^(log_b a)` for all `n = b^k`.

Here `T` and `f` are indexed by the exponent `k`, i.e. `T k` stands for `T(b^k)`. -/
theorem master_theorem_case1
    (a b C ε : ℝ) (T f : ℕ → ℝ)
    (ha : 0 < a) (hb : 1 < b) (hC : 0 ≤ C) (hε : 0 < ε)
    (hT0 : 0 < T 0)
    (hrec : ∀ k, T (k + 1) = a * T k + f (k + 1))
    (hfnn : ∀ k, 0 ≤ f k)
    (hfO : ∀ k, f k ≤ C * (b ^ (k : ℝ)) ^ (Real.logb b a - ε)) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ k : ℕ,
      c₁ * (b ^ (k : ℝ)) ^ (Real.logb b a) ≤ T k ∧
      T k ≤ c₂ * (b ^ (k : ℝ)) ^ (Real.logb b a) := by
  have hb0 : (0:ℝ) < b := lt_trans zero_lt_one hb
  set d : ℝ := b ^ (-ε) with hd
  have hd0 : 0 < d := Real.rpow_pos_of_pos hb0 _
  have hd1 : d < 1 := by
    rw [hd]
    exact Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
  refine ⟨T 0, T 0 + C / (1 - d), hT0, ?_, ?_⟩
  · have : 0 ≤ C / (1 - d) := div_nonneg hC (by linarith)
    linarith
  · intro k
    rw [rpow_logb_pow ha hb k]
    constructor
    · rw [mul_comm]
      exact master_lower ha hrec hfnn k
    · have hup := master_upper_aux (T := T) (f := f) ha hb hC hε hrec hfO k
      have hdk : 0 < d ^ k := pow_pos hd0 k
      have hdk1 : d ^ k ≤ 1 := pow_le_one₀ hd0.le hd1.le
      have hBn : 0 ≤ C / (1 - d) := div_nonneg hC (by linarith)
      have hak : (0:ℝ) < a ^ k := pow_pos ha k
      have : T 0 + C / (1 - d) * (1 - d ^ k) ≤ T 0 + C / (1 - d) := by
        nlinarith
      calc T k ≤ a ^ k * (T 0 + C / (1 - d) * (1 - d ^ k)) := hup
        _ ≤ a ^ k * (T 0 + C / (1 - d)) := by
            exact mul_le_mul_of_nonneg_left this hak.le
        _ = (T 0 + C / (1 - d)) * a ^ k := by ring

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

