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
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed immediately after `import Mathlib` because Lean 4
requires `import` commands to precede every other command, including module
docstrings; the header text itself is verbatim.)
-/

set_option maxHeartbeats 1000000

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

lemma one_lt_cullen {n : ℕ} (hn : 1 ≤ n) : 1 < cullen n := by
  have : 1 * 2 ^ 1 ≤ n * 2 ^ n :=
    Nat.mul_le_mul hn (Nat.pow_le_pow_right (by norm_num) hn)
  simp only [cullen_def]
  omega

/-- A number bigger than `1` with no prime factor `p` satisfying `p * p ≤ m` is prime. -/
