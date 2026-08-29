import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- `A` contains an arithmetic progression of length `k`: there are a starting point `a`
and a positive common difference `d` with `a, a + d, …, a + (k-1) d` all in `A`. -/

theorem not_summable_one_div_primeSet :
    ¬ Summable (Set.indicator primeSet (fun n : ℕ ↦ (1 : ℝ) / n)) :=
  not_summable_one_div_on_primes

/-- **Green–Tao, as a Lean-checked reduction.**
The Erdős–Turán statement implies that the primes contain arbitrarily long arithmetic
progressions.  The reduction uses the (unconditional, Mathlib) divergence of the sum of
the reciprocals of the primes. -/
