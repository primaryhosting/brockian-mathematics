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

import Mathlib
/-!
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Filter Topology

/-- `logicalError C p k` is the effective (logical) error rate of a physical error rate `p`
after `k` levels of code concatenation, where one level of concatenation maps an error rate
`q` to `C * q ^ 2` (a block of the code fails only when at least two of its components fail,
and `C` counts the number of such failing pairs of locations). -/
noncomputable def logicalError (C p : ℝ) : ℕ → ℝ
  | 0 => p
  | k + 1 => C * (logicalError C p k) ^ 2

@[simp] theorem logicalError_zero (C p : ℝ) : logicalError C p 0 = p := rfl

@[simp] theorem logicalError_succ (C p : ℝ) (k : ℕ) :
    logicalError C p (k + 1) = C * (logicalError C p k) ^ 2 := rfl

/-- Closed form for the concatenation recursion: `C * p_k = (C * p) ^ (2 ^ k)`. -/
theorem mul_logicalError (C p : ℝ) (k : ℕ) :
    C * logicalError C p k = (C * p) ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have : C * logicalError C p (k + 1) = (C * logicalError C p k) ^ 2 := by
        simp only [logicalError_succ]; ring
      rw [this, ih, ← pow_mul, pow_succ]

/-- Explicit doubly-exponential suppression of the logical error rate. -/
theorem logicalError_eq (C p : ℝ) (hC : C ≠ 0) (k : ℕ) :
    logicalError C p k = (C * p) ^ (2 ^ k) / C := by
  rw [← mul_logicalError C p k]
  field_simp

/-- The logical error rate stays nonnegative below threshold. -/
theorem logicalError_nonneg {C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p) (k : ℕ) :
    0 ≤ logicalError C p k := by
  induction k with
  | zero => simpa using hp
  | succ k ih => exact mul_nonneg hC (sq_nonneg _)

/--
**Threshold theorem** (statement, in the standard concatenated-code form).

For a fault-tolerant scheme whose one level of concatenation suppresses errors according to
`p ↦ C * p ^ 2` there is a strictly positive constant error threshold `p_th` (namely `1 / C`)
such that for every physical error rate `p` below the threshold:

* the logical error rate after `k` levels of concatenation tends to `0` as `k → ∞`;
* consequently, any quantum computation consisting of `N` gate locations can be simulated
  to within any desired total error `ε > 0` by using enough (finitely many) levels of
  concatenation.
-/
theorem threshold_theorem (C : ℝ) (hC : 0 < C) :
    ∃ p_th : ℝ, 0 < p_th ∧ ∀ p : ℝ, 0 ≤ p → p < p_th →
      Tendsto (logicalError C p) atTop (𝓝 0) ∧
      ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, (N : ℝ) * logicalError C p k < ε := by
  refine ⟨1 / C, by positivity, fun p hp hlt => ?_⟩
  set q : ℝ := C * p with hq
  have hq0 : 0 ≤ q := mul_nonneg hC.le hp
  have hq1 : q < 1 := by
    rw [hq]
    calc C * p < C * (1 / C) := by
          exact mul_lt_mul_of_pos_left hlt hC
      _ = 1 := by field_simp
  have hpow : Tendsto (fun k : ℕ => q ^ (2 ^ k)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hmain : Tendsto (logicalError C p) atTop (𝓝 0) := by
    have heq : logicalError C p = fun k : ℕ => q ^ (2 ^ k) / C :=
      funext fun k => logicalError_eq C p hC.ne' k
    rw [heq]
    simpa using hpow.div_const C
  refine ⟨hmain, fun N ε hε => ?_⟩
  have hNc : Tendsto (fun k => (N : ℝ) * logicalError C p k) atTop (𝓝 0) := by
    simpa using hmain.const_mul (N : ℝ)
  have : ∀ᶠ k in atTop, (N : ℝ) * logicalError C p k < ε := by
    have := hNc (Iio_mem_nhds hε)
    simpa [Set.mem_Iio] using this
  exact this.exists

end QI

