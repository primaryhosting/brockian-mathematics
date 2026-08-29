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

lemma exists_pow_two_gt (t : ℝ) (ht : 0 ≤ t) :
    ∃ L : ℕ, t < (2 : ℝ) ^ L ∧ (2 : ℝ) ^ L ≤ 2 * t + 2 := by
  set n : ℕ := ⌊t⌋₊ + 1 with hn
  have hn1 : 1 ≤ n := Nat.le_add_left 1 _
  refine ⟨Nat.clog 2 n, ?_, ?_⟩
  · have h1 : t < (n : ℝ) := by
      have := Nat.lt_floor_add_one t
      simpa [hn] using this
    have h2 : (n : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 n := by
      have := Nat.le_pow_clog (b := 2) (by norm_num) n
      exact_mod_cast this
    linarith
  · rcases eq_or_lt_of_le hn1 with h | h
    · -- `n = 1`, so `Nat.clog 2 n = 0`
      have hzero : Nat.clog 2 n = 0 := by rw [← h]; simp
      rw [hzero, pow_zero]
      linarith
    · have hlt : 2 ^ (Nat.clog 2 n).pred < n :=
        Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
      have hpos : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) h
      have hsucc : (Nat.clog 2 n).pred + 1 = Nat.clog 2 n := Nat.succ_pred_eq_of_pos hpos
      have hsplit : 2 ^ Nat.clog 2 n = 2 ^ (Nat.clog 2 n).pred * 2 := by
        conv_lhs => rw [← hsucc]
        rw [pow_succ]
      have hnat : 2 ^ Nat.clog 2 n ≤ 2 * n := by omega
      have hcast : (2 : ℝ) ^ Nat.clog 2 n ≤ 2 * (n : ℝ) := by exact_mod_cast hnat
      have hfl : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht
      have hnr : ((n : ℕ) : ℝ) = (⌊t⌋₊ : ℝ) + 1 := by push_cast [hn]; ring
      rw [hnr] at hcast
      linarith

/-- The key estimate: if `2 ^ L` exceeds `log (1 / (c ε)) / log (1 / (c p))` then the
level-`L` logical error rate is below `ε`. -/
