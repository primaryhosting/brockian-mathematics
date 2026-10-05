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

lemma two_pow_modEq (r n : ℕ) (hr : r < 36) :
    (2 : ℕ) ^ n ≡ 2 ^ (n % 36) [MOD coverPrime r] := by
  conv_lhs => rw [← Nat.div_add_mod n 36, pow_add, pow_mul]
  calc ((2 : ℕ) ^ 36) ^ (n / 36) * 2 ^ (n % 36)
      ≡ 1 ^ (n / 36) * 2 ^ (n % 36) [MOD coverPrime r] :=
        Nat.ModEq.mul_right _ (Nat.ModEq.pow _ (two_pow_36_modEq_one r hr))
    _ = 2 ^ (n % 36) := by rw [one_pow, one_mul]

/-- The covering property: for every `n`, the prime `coverPrime (n % 36)` divides
`78557 * 2 ^ n + 1`. -/
