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

theorem Green_Tao_base_three : HasAPOfLength primeSet 3 :=
  Green_Tao_base_le_ten (by norm_num)

/-! ### Sub-progressions and the "infinitely many" form of the statement -/

/-- A progression of length `j + k` contains a progression of length `k` whose first term is
at least `j`: just start `j` steps later. -/
