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

lemma coverPrime_le (r : ℕ) : coverPrime r ≤ 73 := by
  have h : ∀ s < 36, coverPrime s ≤ 73 := by decide
  rcases lt_or_ge r 36 with hr | hr
  · exact h r hr
  · rw [coverPrime_of_ge r hr]; norm_num

/-- Each prime of the covering set has multiplicative order dividing `36`,
i.e. it divides `2 ^ 36 - 1`. -/
