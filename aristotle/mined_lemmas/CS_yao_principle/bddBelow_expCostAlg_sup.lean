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

open Set

variable {A I : Type*} [Fintype A] [Fintype I]

/-- The expected cost of the randomized algorithm given by the distribution `p` over the
deterministic algorithms `A`, run on the input `i`. -/

lemma bddBelow_expCostAlg_sup [Nonempty A] [Nonempty I] (c : A → I → ℝ) :
    BddBelow (Set.range fun p : stdSimplex ℝ A => ⨆ i, expCostAlg c (p : A → ℝ) i) := by
  refine ⟨⨅ x : A × I, c x.1 x.2, ?_⟩
  rintro _ ⟨p, rfl⟩
  have hm : ∀ x : A × I, (⨅ x : A × I, c x.1 x.2) ≤ c x.1 x.2 := fun x =>
    ciInf_le (Finite.bddBelow_range fun x : A × I => c x.1 x.2) x
  have h1 : (⨅ x : A × I, c x.1 x.2) ≤ expCostAlg c (p : A → ℝ) (Classical.arbitrary I) :=
    le_wsum p.2 fun a => hm (a, Classical.arbitrary I)
  exact h1.trans (le_ciSup (Finite.bddAbove_range _) (Classical.arbitrary I))

