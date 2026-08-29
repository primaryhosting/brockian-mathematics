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
# Pair 10007 10009
Category: Frontier — Prime Numbers
Target: Twin.pair_10007_10009
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pair 10007 10009
Category: Frontier — Prime Numbers
Target: Twin.pair_10007_10009
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Twin

/-- 10007 and 10009 form a twin prime pair. -/
theorem pair_10007_10009 :
    Nat.Prime 10007 ∧ Nat.Prime 10009 ∧ 10009 = 10007 + 2 :=
  ⟨by norm_num, by norm_num, by norm_num⟩

end Twin

