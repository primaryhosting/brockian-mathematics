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

private lemma two_mul_eq (d : ℕ) (hd : 0 < d) (hb : 2 * d ≤ 12) : f (2 * d) = -f d := by
  have h2 := h d 2 hd (by norm_num) (by omega)
  have e : apSum f d 2 = f d + f (2 * d) := by
    simp [apSum, Finset.sum_Icc_succ_top]
  rcases hf d hd with h1 | h1 <;> rcases hf (2 * d) (by positivity) with h3 | h3 <;>
    rw [e, h1, h3] at h2 <;> simp_all

/-- Under a discrepancy bound of `1`, `f (3 d) = - f d`. -/
