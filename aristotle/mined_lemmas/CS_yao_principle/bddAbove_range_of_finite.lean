/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to come before any module docstring, so the required header appears
-- at the top of the file as a plain comment and again here as the module docstring.)

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

variable {A I : Type*} [Fintype A] [Fintype I] [Nonempty A] [Nonempty I]

/-- The worst-case expected cost of the randomized algorithm given by the distribution `p`
over deterministic algorithms:  `max over inputs i of  E_{a ~ p} [c a i]`. -/

lemma bddAbove_range_of_finite {ι : Type*} [Finite ι] (f : ι → ℝ) : BddAbove (Set.range f) :=
  (Set.finite_range f).bddAbove

