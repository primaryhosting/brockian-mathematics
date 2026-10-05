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
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` lines to precede every other command, including module
docstrings, so the requested header comment appears immediately after the import.)
-/

open scoped BigOperators

namespace Brockian.GoldbachComb

/-- The Goldbach representation count of `n`: the number of ordered pairs `(a, n - a)`
with `a ≤ n` such that both `a` and `n - a` are prime. -/

noncomputable def primeIndicator (a : ℕ) : ℝ := if Nat.Prime a then 1 else 0

/-- **Transfer identity (general weights).**  For any real weight `f`, the partial sums of the
additive self-correlation of `f` (the "Goldbach convolution") coincide with the bilinear
(covariance-type) sum of `f ⊗ f` over the triangle `{(p, q) : p + q ≤ N}`. -/
