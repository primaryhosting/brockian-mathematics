/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is repeated as a module docstring below; Lean requires `import`
-- to precede any module docstring.)

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
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

variable {A I : Type*}

/-- The expected cost of the randomized algorithm given by the distribution `p` over the
(deterministic) algorithms `A`, run on the input `i`. -/

lemma bddAbove_minDist (cost : A → I → ℝ) :
    BddAbove (Set.range fun q : stdSimplex ℝ I => ⨅ a, distCost cost a (q : I → ℝ)) := by
  obtain ⟨m, M, hm⟩ := exists_cost_bounds cost
  refine ⟨M, ?_⟩
  rintro _ ⟨q, rfl⟩
  obtain ⟨a⟩ := ‹Nonempty A›
  refine le_trans (ciInf_le (bddBelow_distCost cost (q : I → ℝ)) a) ?_
  exact convex_comb_le q.2 fun i => (hm a i).2

/-- Weak duality: the distributional complexity is at most the randomized complexity. -/
