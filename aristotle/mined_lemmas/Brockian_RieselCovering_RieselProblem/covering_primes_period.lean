import Brockian.RieselCovering

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
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.RieselCovering

/-- A *Riesel number* is an odd natural number `k` such that `k * 2 ^ n - 1` is composite
(equivalently, not prime, since these numbers are `> 1`) for every `n ≥ 1`. -/

theorem covering_primes_period {p : ℕ} (hp : p ∈ [3, 5, 7, 13, 17, 241]) :
    p.Prime ∧ p ≤ 241 ∧ p ∣ 2 ^ 24 - 1 := by
  fin_cases hp <;> refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **509203 is a Riesel number**: it is odd, and `509203 * 2 ^ n - 1` is never prime
for `n ≥ 1`.  This is Riesel's classical construction, proved here via the covering
system `{3, 5, 7, 13, 17, 241}` of period `24`. -/
