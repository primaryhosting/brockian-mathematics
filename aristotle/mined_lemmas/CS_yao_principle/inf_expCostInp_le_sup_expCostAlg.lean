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

lemma inf_expCostInp_le_sup_expCostAlg [Nonempty A] [Nonempty I] (c : A → I → ℝ)
    {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A) {q : I → ℝ} (hq : q ∈ stdSimplex ℝ I) :
    (⨅ a, expCostInp c q a) ≤ ⨆ i, expCostAlg c p i := by
  have h1 : (⨅ a, expCostInp c q a) ≤ ∑ a, p a * expCostInp c q a :=
    le_wsum hp fun a => ciInf_le (Finite.bddBelow_range _) a
  have h2 : ∑ i, q i * expCostAlg c p i ≤ ⨆ i, expCostAlg c p i :=
    wsum_le hq fun i => le_ciSup (Finite.bddAbove_range _) i
  rw [exchange p q] at h2
  linarith

end Basic

/-- **Key separation lemma.** If every randomized algorithm has expected cost more than `v`
on some input, then there is a single input distribution `q` against which *every* deterministic
algorithm has expected cost more than `v`. -/
