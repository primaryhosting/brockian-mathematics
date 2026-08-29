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
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace SierpinskiCovering

/-- The covering set assignment: for a residue `r` of the exponent modulo `36`,
`coverPrime r` is a prime from Selfridge's covering set
`{3, 5, 7, 13, 19, 37, 73}` that divides `78557 * 2 ^ n + 1` whenever `n % 36 = r`. -/

lemma two_pow_36_modEq_one (r : ℕ) (hr : r < 36) :
    (2 : ℕ) ^ 36 ≡ 1 [MOD coverPrime r] := by
  have h : ∀ s < 36, 2 ^ 36 % coverPrime s = 1 % coverPrime s := by decide
  exact h r hr

/-- Since `2 ^ 36 ≡ 1`, the powers of two modulo a covering prime are `36`-periodic. -/
