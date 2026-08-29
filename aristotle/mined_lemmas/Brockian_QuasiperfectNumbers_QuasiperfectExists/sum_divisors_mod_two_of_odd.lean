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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean requires `import` commands to precede every other command, including
module doc comments, so the header above is a plain comment and is repeated as the
module docstring after the import below.)
-/

import Mathlib

/-!
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if the sum of all its divisors equals `2 * n + 1`,
i.e. `σ n = 2n + 1`.  Whether a quasiperfect number exists is an open problem. -/

theorem sum_divisors_mod_two_of_odd {m : ℕ} (hm : Odd m) :
    (∑ d ∈ m.divisors, d) % 2 = (m.divisors.card) % 2 := by
  rw [Finset.sum_nat_mod]
  congr 1
  rw [Finset.sum_congr rfl (fun d hd => ?_), Finset.sum_const, smul_eq_mul, mul_one]
  have : Odd d := odd_of_dvd_odd hm (Nat.dvd_of_mem_divisors hd)
  exact Nat.odd_iff.mp this

/-- A positive number with an odd number of divisors is a perfect square. -/
