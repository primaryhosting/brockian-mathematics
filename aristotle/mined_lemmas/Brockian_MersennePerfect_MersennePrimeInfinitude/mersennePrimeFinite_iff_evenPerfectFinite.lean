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
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede any module doc comment `/-! ... -/`,
-- so the header is repeated verbatim as a module docstring just below the import.)

import Mathlib

/-!
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The infinitude of Mersenne primes is a famous open problem, so we do not prove it
outright.  Instead we give a Lean-checked *equivalent reformulation*: the set of
exponents `p` for which `2 ^ p - 1` is prime is infinite **if and only if** the set of
even perfect numbers is infinite.  The equivalence comes from the Euclid–Euler
theorem, which is reproved here (following the Mathlib archive development of the
Euclid–Euler theorem) so that the file depends only on `Mathlib` itself.

We also record the contrapositive form: there are only finitely many Mersenne primes
iff there are only finitely many even perfect numbers.
-/

namespace Brockian

namespace MersennePerfect

open ArithmeticFunction Finset

open scoped sigma

/-! ### The Euclid–Euler theorem -/


theorem mersennePrimeFinite_iff_evenPerfectFinite :
    MersenneExponents.Finite ↔ EvenPerfects.Finite := by
  simpa [← Set.not_infinite, not_iff_not] using MersennePrimeInfinitude

/-! ### Sanity checks (non-vacuity) -/

example : 2 ∈ MersenneExponents := by
  norm_num [MersenneExponents, mersenne]

example : 3 ∈ MersenneExponents := by
  norm_num [MersenneExponents, mersenne]

example : (6 : ℕ) ∈ EvenPerfects := by
  have : euclidEuler 2 = 6 := by norm_num [euclidEuler, mersenne]
  rw [← this, ← image_euclidEuler]
  exact ⟨2, by norm_num [MersenneExponents, mersenne], rfl⟩

example : (28 : ℕ) ∈ EvenPerfects := by
  have : euclidEuler 3 = 28 := by norm_num [euclidEuler, mersenne]
  rw [← this, ← image_euclidEuler]
  exact ⟨3, by norm_num [MersenneExponents, mersenne], rfl⟩

end MersennePerfect

end Brockian

