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
-/

/-
Note on file layout: Lean 4 requires all `import` commands to appear before any
other command, including module docstrings, so the mandated header comment above
is placed immediately after the single `import Mathlib` line.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th **Cullen number** `C n = n * 2 ^ n + 1`. -/

theorem three_le_cullen {n : ℕ} (hn : 1 ≤ n) : 3 ≤ cullen n := by
  have h2 : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : 1 * 2 ≤ n * 2 ^ n := Nat.mul_le_mul hn (by simpa using h2)
  simp only [cullen]
  omega

/-- A trial-division criterion: if no prime `q` with `q ^ 2 ≤ C n` divides `C n`,
then `C n` is prime. -/
