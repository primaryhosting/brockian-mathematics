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

lemma tendsto_errorAtLevel {c p : ℝ} (hc : 0 < c) (hp0 : 0 ≤ p) (hcp : c * p < 1) :
    Filter.Tendsto (fun L : ℕ => errorAtLevel c p L) Filter.atTop (nhds 0) := by
  have hq0 : 0 ≤ c * p := mul_nonneg hc.le hp0
  have hmain : Filter.Tendsto (fun L : ℕ => (c * p) ^ L / c) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hcp).div_const c
  refine squeeze_zero (fun L => ?_) (fun L => ?_) hmain
  · unfold errorAtLevel
    positivity
  · unfold errorAtLevel
    have hle : (c * p) ^ (2 ^ L) ≤ (c * p) ^ L :=
      pow_le_pow_of_le_one hq0 hcp.le (Nat.le_of_lt Nat.lt_two_pow_self)
    exact div_le_div_of_nonneg_right hle hc.le

/-- **Threshold theorem.**  For a fault-tolerance scheme with threshold constant `c > 0`
and gadget size `d ≤ 2 ^ k` there is a strictly positive error threshold `p_th = 1 / c`
such that for every physical error rate `p < p_th`:

* the logical error rates `errorAtLevel c p L` obey the concatenation recursion
  `p_0 = p`, `p_{L+1} = c * p_L ^ 2`;
* they tend to `0` as the number `L` of concatenation levels grows;
* consequently every target accuracy `ε > 0` is reached at some finite level `L`, and the
  physical overhead `d ^ L` of one logical operation is bounded by a fixed power of
  `2 + 2 log(1/(cε)) / log(1/(cp))`, i.e. it is polylogarithmic in `1/ε`.

Thus, below the constant error threshold, arbitrarily accurate fault-tolerant quantum
computation is possible with only polylogarithmic overhead. -/
