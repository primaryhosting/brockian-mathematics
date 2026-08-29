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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LandauNSquaredPlusOne

open Zsqrtd

/-- A *Landau prime* is a prime natural number of the form `n ^ 2 + 1`. -/

theorem landauFourth_iff_gaussian : LandauFourthStatement ↔ GaussianPrimeFormulation := by
  rw [LandauFourthStatement, GaussianPrimeFormulation, landauPrimes_eq_image]
  exact Set.infinite_image_iff (fun a _ b _ hab => by simpa using hab)

/-- **Landau's fourth conjecture**, conditional on its Gaussian reformulation:
if there are infinitely many Gaussian primes of the form `n + i` (`n : ℕ`), then there
are infinitely many rational primes of the form `n ^ 2 + 1`.

Landau's fourth problem is a well-known open problem; what is established here is a
Lean-checked reduction of it to a statement about Gaussian primes, which
`landauFourth_iff_gaussian` shows to be equivalent to it. -/
