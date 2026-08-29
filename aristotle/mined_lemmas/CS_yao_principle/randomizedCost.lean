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

noncomputable def randomizedCost [Nonempty I] (c : A → I → ℝ) (p : A → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (expectedCost c p)

/-- The distributional cost of the input distribution `q`: the cost of the best deterministic
algorithm against `q`. -/
