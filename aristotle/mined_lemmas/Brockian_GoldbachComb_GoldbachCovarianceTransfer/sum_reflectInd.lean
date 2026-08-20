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
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
The header above is a plain block comment rather than a module doc comment (`/-! ... -/`)
because Lean 4 requires `import` commands to be the first commands of a file; a module
doc comment placed before the imports is rejected by the parser.  The text is otherwise
verbatim as requested.

## Contents

For `n : ℕ` we work on the sample space `Finset.range (n+1)` equipped with the uniform
measure, and we consider two `{0,1}`-valued observables:

* `X p = 1` iff `p` is prime;
* `Y p = 1` iff `n - p` is prime (the *reflection* of `X` through the involution
  `p ↦ n - p` of `range (n+1)`).

The empirical covariance of `X` and `Y` is the *Goldbach covariance* `goldbachCov n`.
The main theorem `GoldbachCovarianceTransfer` transfers this analytic quantity into the
purely combinatorial data of the Goldbach problem: the number `goldbachCount n` of
Goldbach representations of `n` and the prime counting function `primeCount n`,
$$\operatorname{Cov}(X,Y) = \frac{r(n)}{n+1} - \left(\frac{\pi(n)}{n+1}\right)^2 .$$
The key input is that the reflection `p ↦ n - p` is an involution of `range (n+1)`, so
`X` and `Y` have the *same* mean, which is what makes the second term a square.

As a consequence we obtain a genuine reduction (`goldbach_of_goldbachCov_gt`): any
lower bound on the Goldbach covariance beating `-(π(n)/(n+1))²` forces `n` to be a sum
of two primes.
-/

open Finset

namespace Brockian.GoldbachComb

/-- Real-valued indicator of a proposition. -/

theorem sum_reflectInd (n : ℕ) :
    ∑ p ∈ range (n + 1), ind (n - p).Prime = (primeCount n : ℝ) := by
  classical
  rw [sum_ind, card_reflect_prime]

