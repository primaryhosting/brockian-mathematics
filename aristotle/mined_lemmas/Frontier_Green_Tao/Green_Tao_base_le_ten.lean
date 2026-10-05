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

theorem Green_Tao_base_le_ten {k : ℕ} (hk : k ≤ 10) : HasAPOfLength primeSet k := by
  refine ⟨199, 210, by norm_num, fun i hi ↦ ?_⟩
  have hi10 : i < 10 := lt_of_lt_of_le hi hk
  interval_cases i <;> simp only [primeSet, Set.mem_setOf_eq] <;> norm_num

/-- Unconditional base cases, longer version: the primes contain arithmetic progressions of
every length `k ≤ 13`, witnessed by `766439 + 510510 i`. -/
