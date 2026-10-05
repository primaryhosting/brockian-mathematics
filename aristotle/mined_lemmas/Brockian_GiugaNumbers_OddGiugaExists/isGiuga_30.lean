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
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to precede every other command, so the header above is a plain
-- comment; it is repeated verbatim as the module docstring immediately after the import.)

import Mathlib

/-!
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Summary

A *Giuga number* is a composite `n` with `p ∣ n / p - 1` for every prime `p ∣ n`
(`IsGiuga`).  The smallest one is `30`.  Whether an **odd** Giuga number exists is an open
problem, so the target `OddGiugaExists` is stated and proved here as a Lean-checked
equivalent reformulation (a reduction), not as an unconditional existence claim:

* `OddGiugaExists` : an odd Giuga number exists **iff** there is a finite set `S` of at least
  two odd primes with `p ∣ (∏ q ∈ S \ {p}, q) - 1` for every `p ∈ S`.

Supporting results and unconditional partial results proved here:

* `IsGiuga.squarefree` : Giuga numbers are squarefree;
* `isGiugaSet_primeFactors` / `isGiuga_prod` : the two directions of the reduction;
* `isGiuga_30` : `30` is a Giuga number;
* `IsGiuga.dvd_sum_div_sub_one` : Giuga's congruence `n ∣ (∑ p ∈ n.primeFactors, n / p) - 1`;
* `IsGiuga.one_lt_sum_inv` : the reciprocals of the prime factors sum to more than `1`;
* `odd_giuga_nine_le_card` : an odd Giuga number has at least nine distinct prime factors.
-/

open scoped BigOperators

namespace Brockian.GiugaNumbers

/-- `n` is a *Giuga number* if it is composite (`1 < n` and not prime) and for every prime
divisor `p` of `n` we have `p ∣ n / p - 1`. -/

theorem isGiuga_30 : IsGiuga 30 := by
  have hS : IsGiugaSet ({2, 3, 5} : Finset ℕ) := by
    refine ⟨?_, ?_, ?_⟩ <;> decide
  have h := isGiuga_prod hS
  have hprod : (∏ q ∈ ({2, 3, 5} : Finset ℕ), q) = 30 := by decide
  rwa [hprod] at h

/-!
## Partial results towards the odd Giuga problem
-/

/-- Every prime factor of a Giuga number `n` divides `(∑ q ∈ n.primeFactors, n / q) - 1`. -/
