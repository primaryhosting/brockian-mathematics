/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Statement: Yao's minimax principle relates randomized and distributional complexity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Statement: Yao's minimax principle relates randomized and distributional complexity.
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

namespace CS

variable {A I : Type*} [Fintype A] [Nonempty A] [Fintype I] [Nonempty I]

/-- The expected cost of the randomized algorithm given by the mixed strategy `p`
(a distribution over the deterministic algorithms `A`) on the worst-case input. -/

lemma distributionalComplexity_le (C : A → I → ℝ) :
    distributionalComplexity C ≤ randomizedComplexity C :=
  ciSup_le fun q => le_ciInf fun p => weak_duality C p.2 q.2

/-! ### The linear map given by the cost matrix -/

/-- The linear map sending a mixed strategy `p` over algorithms to the vector of
expected costs on each input. -/
