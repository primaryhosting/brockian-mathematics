/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The discrepancy sum of the sequence `f` along the homogeneous arithmetic progression
of common difference `d` and length `n`, i.e. `f d + f (2 d) + ... + f (n d)`. -/

private lemma five_mul_eq (d : ℕ) (hd : 0 < d) (hb : 6 * d ≤ 12) : f (5 * d) = -f d := by
  have h6 := h d 6 hd (by norm_num) (by omega)
  have e : apSum f d 6 =
      f d + f (2 * d) + f (3 * d) + f (4 * d) + f (5 * d) + f (6 * d) := by
    simp [apSum, Finset.sum_Icc_succ_top]
  have e2 : f (2 * d) = -f d := two_mul_eq hf h d hd (by omega)
  have e3 : f (3 * d) = -f d := three_mul_eq hf h d hd (by omega)
  have e4 : f (4 * d) = f d := by
    have := two_mul_eq hf h (2 * d) (by positivity) (by omega)
    rw [← Nat.mul_assoc] at this
    norm_num at this
    rw [this, e2, neg_neg]
  have e6 : f (6 * d) = f d := by
    have := two_mul_eq hf h (3 * d) (by positivity) (by omega)
    rw [← Nat.mul_assoc] at this
    norm_num at this
    rw [this, e3, neg_neg]
  rw [e, e2, e3, e4, e6] at h6
  have hsum : |f (5 * d) + f d| ≤ 1 := by
    have : f d + -f d + -f d + f d + f (5 * d) + f d = f (5 * d) + f d := by ring
    rwa [this] at h6
  rcases hf d hd with h1 | h1 <;> rcases hf (5 * d) (by positivity) with h5 | h5 <;>
    rw [h1, h5] at hsum <;> simp_all

/-- A `±1` sequence cannot have all homogeneous-progression discrepancies bounded by `1`. -/
