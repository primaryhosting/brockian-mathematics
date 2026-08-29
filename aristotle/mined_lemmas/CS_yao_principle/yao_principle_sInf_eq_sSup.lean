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

theorem yao_principle_sInf_eq_sSup [Nonempty A] [Nonempty I] (c : A → I → ℝ) :
    sInf (randomizedCost c '' stdSimplex ℝ A) = sSup (distributionalCost c '' stdSimplex ℝ I) := by
  obtain ⟨p, -, q, -, hleast, hgreatest, heq⟩ := yao_principle c
  rw [hleast.csInf_eq, hgreatest.csSup_eq, heq]

end Yao

end CS

