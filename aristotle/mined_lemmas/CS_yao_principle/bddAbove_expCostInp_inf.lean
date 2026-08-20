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

lemma bddAbove_expCostInp_inf [Nonempty A] [Nonempty I] (c : A → I → ℝ) :
    BddAbove (Set.range fun q : stdSimplex ℝ I => ⨅ a, expCostInp c (q : I → ℝ) a) := by
  refine ⟨⨆ x : A × I, c x.1 x.2, ?_⟩
  rintro _ ⟨q, rfl⟩
  have hM : ∀ x : A × I, c x.1 x.2 ≤ ⨆ x : A × I, c x.1 x.2 := fun x =>
    le_ciSup (Finite.bddAbove_range fun x : A × I => c x.1 x.2) x
  have h1 : expCostInp c (q : I → ℝ) (Classical.arbitrary A) ≤ ⨆ x : A × I, c x.1 x.2 :=
    wsum_le q.2 fun i => hM (Classical.arbitrary A, i)
  exact le_trans (ciInf_le (Finite.bddBelow_range _) (Classical.arbitrary A)) h1

/-- Weak duality: for any randomized algorithm `p` and any input distribution `q`, the best
deterministic algorithm against `q` does no worse than `p` does in the worst case. -/
