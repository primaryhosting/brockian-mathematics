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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `IsKHyperperfect k n` states that `n` is a `k`-hyperperfect number, i.e. `k > 0`, `n > 1` and
`n = 1 + k * (σ n - n - 1)`, written here in the subtraction-free form
`k * σ n + 1 = (k + 1) * n + k`. -/

theorem isHyperperfect_threehundredone : IsHyperperfect 301 :=
  ⟨6, by refine ⟨by norm_num, by norm_num, ?_⟩; decide⟩

/-- **Hyperperfect Infinitude (conditional reduction).**

Assume the (open) hypothesis `H`: for every bound `N` there is some `k > N` such that `k + 1`
is prime and `(k + 1) ^ (j + 1) - k` is prime for some `j ≥ 1`.  Then there are infinitely many
hyperperfect numbers.

The hypothesis is stated in subtraction-free form: `p + k = (k + 1) ^ (j + 1)` with `p` prime.
It holds e.g. for `j = 1` whenever `q = k + 1` and `q ^ 2 - q + 1` are both prime
(`q = 2, 3, 7, 13, ...` giving the hyperperfect numbers `6, 21, 301, 2041, ...`). -/
