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

private lemma three_mul_eq (d : ℕ) (hd : 0 < d) (hb : 4 * d ≤ 12) : f (3 * d) = -f d := by
  have h4 := h d 4 hd (by norm_num) (by omega)
  have e : apSum f d 4 = f d + f (2 * d) + f (3 * d) + f (4 * d) := by
    simp [apSum, Finset.sum_Icc_succ_top]
  have e2 : f (2 * d) = -f d := two_mul_eq hf h d hd (by omega)
  have e4 : f (4 * d) = -f (2 * d) := by
    have := two_mul_eq hf h (2 * d) (by positivity) (by omega)
    simpa [← Nat.mul_assoc] using this
  rw [e, e2, e4, e2] at h4
  have hsum : |f (3 * d) + f d| ≤ 1 := by
    have : f d + -f d + f (3 * d) + - -f d = f (3 * d) + f d := by ring
    rwa [this] at h4
  rcases hf d hd with h1 | h1 <;> rcases hf (3 * d) (by positivity) with h3 | h3 <;>
    rw [h1, h3] at hsum <;> simp_all

/-- Under a discrepancy bound of `1`, `f (5 d) = - f d`. -/
