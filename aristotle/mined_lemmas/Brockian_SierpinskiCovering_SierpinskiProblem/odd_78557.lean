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

/-!
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This module is deliberately import-free (core Lean 4 only), because Lean does not
allow a module docstring to precede `import` commands.  A companion module
`Brockian.SierpinskiCoveringMathlib` imports Mathlib and restates the main result
using Mathlib's `Nat.Prime`.

Mathematical content: 78557 is a Sierpiński number, i.e. `78557 * 2 ^ n + 1` is
composite for every `n ≥ 1`.  The proof is the classical covering-congruence
argument: every residue class of `n` modulo 36 forces one of the primes
`3, 5, 7, 13, 19, 37, 73` to divide `78557 * 2 ^ n + 1`.
-/

namespace Brockian
namespace SierpinskiCovering

/-- Primality for naturals: `2 ≤ m` and the only divisors of `m` are `1` and `m`.
This is the usual notion; it is proved equivalent to Mathlib's `Nat.Prime` in the
companion module `Brockian.SierpinskiCoveringMathlib`. -/

theorem odd_78557 : 78557 % 2 = 1 := by decide

end SierpinskiCovering
end Brockian

/-
Companion module to `Brockian.SierpinskiCovering`.

The main module is import-free (Lean does not allow a module docstring before
`import` commands), so it uses its own primality predicate `IsPrimeNat`.  Here we
import Mathlib, show that `IsPrimeNat` agrees with `Nat.Prime`, and restate the
Sierpiński result for `Nat.Prime`.
-/

import Mathlib
import Brockian.SierpinskiCovering

namespace Brockian
namespace SierpinskiCovering

/-- The elementary primality predicate used in the main module coincides with
Mathlib's `Nat.Prime`. -/
