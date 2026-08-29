/-
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-!
## Setting

We formalise the quantitative core of the fault-tolerance threshold theorem for
concatenated quantum error-correcting codes.

A fault-tolerance scheme is described by two constants:

* a *threshold constant* `c > 0`, coming from the combinatorics of the fault-tolerant
  gadget: a level-`(L+1)` gadget fails only if at least two of the level-`L` gadgets it is
  built from fail, which gives the error recursion `p_{L+1} = c * p_L ^ 2`;
* a *gadget size* `d`, the number of level-`L` gadgets used to build one level-`(L+1)`
  gadget, so that one logical operation at concatenation level `L` costs `d ^ L` physical
  operations.

Solving the recursion `p_0 = p`, `p_{L+1} = c * p_L ^ 2` gives the closed form
`p_L = (c * p) ^ (2 ^ L) / c`, which is taken as the definition below and shown to satisfy
the recursion.

The threshold is `p_th = 1 / c`: for any physical error rate `p < p_th` the logical error
rate `p_L` tends to `0` doubly exponentially fast in the number of levels, so an arbitrary
target accuracy `ε` is reached at some finite level, and the physical overhead `d ^ L`
needed is only polylogarithmic in `1 / ε`.
-/

/-- The logical error rate after `L` levels of code concatenation, for a fault-tolerance
scheme with threshold constant `c` and physical error rate `p`.  This is the solution of
the error recursion `p_0 = p`, `p_{L+1} = c * p_L ^ 2`. -/

lemma errorAtLevel_lt_of_lt {c p ε : ℝ} (hc : 0 < c) (hp0 : 0 ≤ p) (hcp : c * p < 1)
    (hε : 0 < ε) (L : ℕ)
    (hL : max 0 (Real.log (1 / (c * ε))) / Real.log (1 / (c * p)) < (2 : ℝ) ^ L) :
    errorAtLevel c p L < ε := by
  set q : ℝ := c * p with hq
  have hq0 : 0 ≤ q := mul_nonneg hc.le hp0
  rcases eq_or_lt_of_le hq0 with hq0' | hqpos
  · -- `p = 0`: the logical error rate vanishes identically
    have hzero : errorAtLevel c p L = 0 := by
      unfold errorAtLevel
      rw [← hq, ← hq0', zero_pow (Nat.two_pow_pos L).ne', zero_div]
    rw [hzero]; exact hε
  · -- `0 < c p < 1`
    have ha : 0 < Real.log (1 / q) := by
      rw [Real.lt_log_iff_exp_lt (by positivity), Real.exp_zero, lt_div_iff₀ hqpos]
      linarith
    set N : ℕ := 2 ^ L with hN
    have hcast : ((N : ℕ) : ℝ) = (2 : ℝ) ^ L := by push_cast [hN]; ring
    have hkey : max 0 (Real.log (1 / (c * ε))) < (N : ℝ) * Real.log (1 / q) := by
      rw [hcast]
      exact (div_lt_iff₀ ha).mp hL
    have hlogq : Real.log (1 / q) = -Real.log q := by rw [one_div, Real.log_inv]
    have hlogce : Real.log (1 / (c * ε)) = -Real.log (c * ε) := by rw [one_div, Real.log_inv]
    rw [hlogq, hlogce] at hkey
    have hle : -Real.log (c * ε) ≤ max 0 (-Real.log (c * ε)) := le_max_right _ _
    have hlt : Real.log (q ^ N) < Real.log (c * ε) := by
      rw [Real.log_pow]
      linarith
    have hqN : q ^ N < c * ε :=
      (Real.log_lt_log_iff (pow_pos hqpos N) (by positivity)).mp hlt
    unfold errorAtLevel
    rw [← hq, ← hN, div_lt_iff₀ hc]
    linarith

/-- Below threshold, any target logical accuracy `ε` is achieved at some concatenation level
`L`, whose size is controlled: `2 ^ L ≤ 2 + 2 log(1/(cε)) / log(1/(cp))`. -/
