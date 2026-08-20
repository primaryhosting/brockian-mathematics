/-
/-!
# Kervaire Invariant
Category: Frontier Math
Target: Math2.kervaire_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the required header
-- appears verbatim above inside a block comment, and again as the module docstring below.)

import Mathlib

/-!
# Kervaire Invariant
Category: Frontier Math
Target: Math2.kervaire_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math2

/-- The set of dimensions allowed by the Hill–Hopkins–Ravenel theorem together with Browder's
theorem: `n = 2 ^ j - 2` with `2 ≤ j ≤ 7`. -/

theorem exponent_le_seven {j : ℕ} (h : 2 ^ j - 2 ≤ 126) : j ≤ 7 := by
  by_contra hcon
  push_neg at hcon
  have h8 : (2 : ℕ) ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hcon
  have : (2 : ℕ) ^ 8 = 256 := by norm_num
  omega

/-- **The Kervaire invariant problem** (statement level).

Let `K n` record the Kervaire invariant of `n`-dimensional framed manifolds (valued in `ZMod 2`);
`K n ≠ 0` says that the Kervaire invariant one problem has a positive answer in dimension `n`.

Feeding in the two known theorems about this invariant —

* Browder's theorem (1969): the Kervaire invariant can be nonzero only in dimensions of the form
  `2 ^ j - 2` with `j ≥ 2`;
* the Hill–Hopkins–Ravenel theorem (2016): the Kervaire invariant vanishes in all dimensions
  `n > 126`;

the Kervaire invariant is nonzero only in the dimensions `2, 6, 14, 30, 62, 126`. -/
