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

set_option grind.warning false

namespace CS

section Yao

variable {A I : Type*} [Fintype A] [Fintype I]

/-- The expected cost of the randomized algorithm given by the distribution `p` over
deterministic algorithms, run on the input `i`. -/

lemma exists_min_randomizedCost [Nonempty A] [Nonempty I] (c : A → I → ℝ) :
    ∃ p ∈ stdSimplex ℝ A, ∀ p' ∈ stdSimplex ℝ A, randomizedCost c p ≤ randomizedCost c p' := by
  obtain ⟨p, hp, hmin⟩ :=
    (isCompact_stdSimplex A).exists_isMinOn
      ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary A)⟩
      (continuous_randomizedCost c).continuousOn
  exact ⟨p, hp, fun p' hp' => isMinOn_iff.mp hmin p' hp'⟩

/-- **Strong duality** (the hard half of Yao's principle): for an optimal randomized algorithm
`p₀` there is an input distribution `q` whose distributional cost is at least the randomized
cost of `p₀`. This is proved by separating the (convex) set of achievable cost vectors from
the open convex set of vectors all of whose coordinates are below the optimal value. -/
