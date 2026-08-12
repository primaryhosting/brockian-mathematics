import Mathlib
import RequestProject.TwoSquares29

/-!
# Two Squares 29, stated with Mathlib's `Nat.Prime`

A restatement of `Math.two_squares_29` using Mathlib's `Nat.Prime` predicate.
-/

namespace Math

/-- The prime `29` is a sum of two squares: `29 = 2 ^ 2 + 5 ^ 2`. -/
theorem two_squares_29_prime : Nat.Prime 29 ∧ ∃ a b : ℕ, 29 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, two_squares_29.2⟩

end Math

/-!
# Two Squares 29
Category: Pure Mathematics
Target: Math.two_squares_29
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 29.** The number `29` is prime (it is at least `2` and has no
divisor strictly between `1` and itself), and it is a sum of two squares,
namely `29 = 2 ^ 2 + 5 ^ 2`.

The statement is phrased with an elementary, import-free description of primality
so that the file can literally begin with the required header comment (a module
documentation comment must precede any `import`, which Lean does not allow).
The file `TwoSquares29Mathlib.lean` re-derives the same result in terms of
Mathlib's `Nat.Prime`. -/
theorem two_squares_29 :
    (2 ≤ 29 ∧ ∀ m : Nat, m < 29 → m ∣ 29 → m = 1) ∧ ∃ a b : Nat, 29 = a ^ 2 + b ^ 2 :=
  ⟨by decide, 2, 5, by decide⟩

end Math

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

