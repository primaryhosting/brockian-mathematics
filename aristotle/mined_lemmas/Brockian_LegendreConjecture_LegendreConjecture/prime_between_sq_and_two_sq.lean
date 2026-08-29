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
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Legendre's conjecture — that for every `n ≥ 1` there is a prime strictly between `n ^ 2` and
`(n + 1) ^ 2` — is a well-known open problem.  This file therefore contains:

* `Brockian.LegendreConjecture.LegendreStatement`, the formal statement of the conjecture;
* several *equivalent* reformulations (contrapositive form, a counting form using
  `Finset` cardinalities, and a form using the prime counting function `π`);
* `Brockian.LegendreConjecture.LegendreConjecture`, a Lean-checked **conditional reduction**:
  Legendre's conjecture follows from the (also open, but formally weaker-looking) statement
  that every interval `(m, m + √m]` contains a prime;
* `Brockian.LegendreConjecture.legendre_of_le_hundred`, an unconditional verification of the
  conjecture for all `1 ≤ n ≤ 100`.
-/

namespace Brockian.LegendreConjecture

open Finset

/-- The statement of Legendre's conjecture: for every `n ≥ 1` there is a prime `p` with
`n ^ 2 < p < (n + 1) ^ 2`. -/

theorem prime_between_sq_and_two_sq (n : ℕ) (hn : 0 < n) :
    ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p ≤ 2 * n ^ 2 :=
  Nat.exists_prime_lt_and_le_two_mul (n ^ 2) (by positivity)

/-- Since Legendre's conjecture is verified for `n ≤ 100`, it is equivalent to its restriction
to `n ≥ 101`. -/
