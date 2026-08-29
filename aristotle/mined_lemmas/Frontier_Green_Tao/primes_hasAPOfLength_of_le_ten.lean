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

theorem primes_hasAPOfLength_of_le_ten (k : ℕ) (hk : k ≤ 10) :
    HasAPOfLength {p : ℕ | Nat.Prime p} k := by
  refine HasAPOfLength.mono (k := 10) ⟨199, 210, by norm_num, ?_⟩ hk
  intro i hi
  interval_cases i <;> norm_num [Set.mem_setOf_eq]

/-- The Erdős conjecture on arithmetic progressions: any set of natural numbers whose
sum of reciprocals diverges contains arbitrarily long arithmetic progressions. -/
