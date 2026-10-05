/-!
# Two Squares 17
Category: Pure Mathematics
Target: Math.two_squares_17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/--
**Two squares for 17.**

`17` is a prime number (it is at least `2` and its only divisors are `1` and `17`),
and it is a sum of two squares, namely `17 = 1 ^ 2 + 4 ^ 2`.

The header comment required for this file is a module docstring, which Lean requires
to come *after* any `import` commands; since the header must be the very first thing in
the file, no imports are possible here and the statement is phrased and proved using
only Lean core, spelling out primality of `17` explicitly instead of using
`Nat.Prime` from Mathlib.
-/
theorem two_squares_17 :
    (2 ≤ 17 ∧ ∀ m : Nat, m ∣ 17 → m = 1 ∨ m = 17) ∧ ∃ a b : Nat, 17 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by omega, ?_⟩, 1, 4, by decide⟩
  intro m h
  have hm : m ≤ 17 := Nat.le_of_dvd (by omega) h
  obtain ⟨k, hk⟩ := h
  match m with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 => omega
  | (n + 18) => omega

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

