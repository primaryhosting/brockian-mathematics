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

/- (Lean requires `import` to be the first command, so this required header is
   given as a plain block comment; it is repeated as a module docstring below.)

# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RieselCovering

/-- Riesel's candidate constant `k = 509203`. -/

lemma pow_two_period {p : ℕ} (h : 2 ^ 24 ≡ 1 [MOD p]) (n : ℕ) :
    2 ^ n ≡ 2 ^ (n % 24) [MOD p] := by
  conv_lhs => rw [← Nat.div_add_mod n 24]
  rw [pow_add, pow_mul]
  calc ((2 ^ 24) ^ (n / 24) * 2 ^ (n % 24))
      ≡ 1 ^ (n / 24) * 2 ^ (n % 24) [MOD p] :=
        Nat.ModEq.mul (Nat.ModEq.pow (n / 24) h) (Nat.ModEq.refl _)
    _ = 2 ^ (n % 24) := by rw [one_pow, one_mul]

/-- The covering congruence: for every `n` some prime of the covering set divides
`509203 * 2 ^ n - 1`. -/
