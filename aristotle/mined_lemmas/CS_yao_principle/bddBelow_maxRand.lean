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

lemma bddBelow_maxRand (cost : A → I → ℝ) :
    BddBelow (Set.range fun p : stdSimplex ℝ A => ⨆ i, randCost cost (p : A → ℝ) i) := by
  obtain ⟨m, M, hm⟩ := exists_cost_bounds cost
  refine ⟨m, ?_⟩
  rintro _ ⟨p, rfl⟩
  obtain ⟨i⟩ := ‹Nonempty I›
  refine le_trans ?_ (le_ciSup (bddAbove_randCost cost (p : A → ℝ)) i)
  exact le_convex_comb p.2 fun a => (hm a i).1

