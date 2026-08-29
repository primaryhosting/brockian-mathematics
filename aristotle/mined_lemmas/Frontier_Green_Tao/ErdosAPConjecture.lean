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
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- `HasAPOfLength S k` says that the set `S ⊆ ℕ` contains a `k`-term arithmetic
progression `a, a + d, …, a + (k-1) d` with positive common difference `d`. -/

def ErdosAPConjecture : Prop :=
  ∀ S : Set ℕ, ¬ Summable (Set.indicator S fun n : ℕ => (1 : ℝ) / n) →
    ∀ k : ℕ, HasAPOfLength S k

/-- **Green–Tao (Lean-checked reduction).**

The primes contain arbitrarily long arithmetic progressions, conditional on the Erdős
conjecture on arithmetic progressions.  The reduction is unconditional and complete: it
combines the hypothesis with the (Mathlib-proved) divergence of the sum of the reciprocals
of the primes.  The unconditional Green–Tao theorem itself is not proved here; see
`Frontier.primes_hasAPOfLength_of_le_ten` for the unconditional base cases `k ≤ 10`. -/
