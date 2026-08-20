/-
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
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

namespace CS

/-- `((b:ℝ)^k) ^ (log_b a + t) = a^k * (b^t)^k` (real powers).
Specializing `t = 0` gives `(b^k)^{log_b a} = a^k`, i.e. `n^{log_b a} = a^k` for `n = b^k`. -/

private lemma geom_partial_sum_le (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (k : ℕ) :
    ∑ i ∈ Finset.range k, r ^ i ≤ (1 - r)⁻¹ := by
  have hm := geom_sum_mul r k
  have hk : (0 : ℝ) ≤ r ^ k := pow_nonneg h0 k
  rw [inv_eq_one_div, le_div_iff₀ (by linarith)]
  nlinarith

/--
**Master theorem, Case 1.**

Let `T (n) = a * T (n / b) + f (n)` be a divide-and-conquer recurrence, considered (as usual)
along the exact powers `n = b ^ k` of the branching factor `b ≥ 2`, with `a ≥ 1` subproblems.
If the combine cost satisfies `f (n) = O (n ^ (log_b a - ε))` for some `ε > 0`
(here with explicit constant `C`), and `f ≥ 0`, `T 1 > 0`, then

  `T (n) = Θ (n ^ (log_b a))`,

i.e. there are positive constants `c₁, c₂` with
`c₁ * n ^ (log_b a) ≤ T n ≤ c₂ * n ^ (log_b a)` for all `n = b ^ k`.
-/
