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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring, so the header above is a
-- plain comment and is repeated below as the module docstring.)

import Mathlib

/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PolignacPrimes

/-- A finite list of linear forms `a * x + b` (encoded as pairs `(a, b)`) is *admissible*
if for every prime `p` there is some `x` for which no form takes a value divisible by `p`. -/

lemma bigPrime_pairwise_coprime (n : ℕ) :
    List.Pairwise (Function.onFun Nat.Coprime (bigPrime n)) (List.range' 1 (n - 1)) := by
  refine List.Pairwise.imp ?_ (List.pairwise_lt_range' (s := 1) (n := n - 1))
  intro i j hij
  exact (Nat.coprime_primes (bigPrime_prime n i) (bigPrime_prime n j)).2
    (ne_of_lt (bigPrime_strictMono n hij))

/-- The key construction: for an even `n > 0` there are `M > 0` and `r` such that the pair of
forms `M x + r`, `M x + r + n` is admissible, and moreover every number strictly between
`M x + r` and `M x + r + n` is composite (for `x ≥ 2`). -/
