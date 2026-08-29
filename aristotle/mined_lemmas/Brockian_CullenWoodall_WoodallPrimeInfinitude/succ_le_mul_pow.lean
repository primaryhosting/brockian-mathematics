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

/-
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Header kept verbatim, except that it is a plain block comment `/- -/` rather than a
-- module docstring `/-! -/`: Lean 4 does not allow any command, including a module
-- docstring, to precede the `import` section of a file.)

import Mathlib

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; for `n ≥ 1`
this agrees with the usual integer definition). -/

lemma succ_le_mul_pow {n : ℕ} (hn : 1 ≤ n) : n + 1 ≤ n * 2 ^ n := by
  have h2 : 2 ≤ 2 ^ n := by
    calc (2:ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  calc n + 1 ≤ n + n := by omega
  _ = n * 2 := by ring
  _ ≤ n * 2 ^ n := Nat.mul_le_mul_left _ h2

/-- Woodall numbers grow at least as fast as the index. -/
