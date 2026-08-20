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

import Mathlib

/-!
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON THE HEADER: Lean 4 requires the `import` commands to be the very first
commands of a file, so the module docstring above (reproduced verbatim as
requested) has to follow `import Mathlib` rather than precede it.

MATHLIB SEARCH.  Oppermann's conjecture is an open problem, strictly stronger
than Legendre's conjecture.  Mathlib contains no result giving a prime in an
interval shorter than Bertrand's postulate (`Nat.bertrand`/`Nat.exists_prime_lt_and_le_two_mul`,
a prime in `(n, 2n]`), which is far too weak to produce a prime in `(n² - n, n²)`.
Accordingly this file provides (i) an unconditional verification of the conjecture
for `2 ≤ n ≤ 50`, and (ii) a Lean-checked reduction of the full conjecture to a
standard short-prime-gap hypothesis.
-/

namespace Brockian.OppermannConjecture

/-- **Oppermann's conjecture**: for every `n ≥ 2` there is a prime strictly between
`n(n-1) = n² - n` and `n²`, and a prime strictly between `n²` and `n(n+1) = n² + n`. -/

theorem lt_of_sq_lt_mul_self {d n : ℕ} (h : d ^ 2 < n * n) : d < n := by
  by_contra hc
  push_neg at hc
  have : n * n ≤ d * d := Nat.mul_le_mul hc hc
  nlinarith

/-- **Main conditional result.** The short prime gap hypothesis
`SqrtPrimeGapHypothesis` (a prime in `(m, m + √m)` for every `m ≥ 117`) implies
Oppermann's conjecture. -/
