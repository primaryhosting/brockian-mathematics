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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.AndricaConjecture

/-!
Andrica's conjecture states that for consecutive primes `pₙ < pₙ₊₁` one has
`√pₙ₊₁ - √pₙ < 1`.  This is an open problem.  What is proved here is a
*conditional reduction*: Andrica's conjecture follows from Oppermann's
conjecture (which is itself open, but is a statement purely about the
distribution of primes in short intervals around squares).
-/

/-- **Oppermann's conjecture**: for every `m ≥ 2` there is a prime strictly between
`m²` and `m² + m`, and a prime strictly between `m² + m` and `(m+1)²`.
(Equivalently, in the usual formulation, a prime between `n(n-1)` and `n²` and one
between `n²` and `n(n+1)` for every `n > 1`.) -/

theorem andrica_of_oppermann (hOpp : Oppermann) : Andrica :=
  AndricaConjecture hOpp

/-- **Legendre's conjecture**: for every `n ≥ 1` there is a prime strictly between `n²`
and `(n+1)²`. -/
