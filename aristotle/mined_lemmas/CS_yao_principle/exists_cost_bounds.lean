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

lemma exists_cost_bounds (cost : A → I → ℝ) :
    ∃ m M : ℝ, ∀ a i, m ≤ cost a i ∧ cost a i ≤ M := by
  obtain ⟨x, hx⟩ := Finite.exists_min (fun x : A × I => cost x.1 x.2)
  obtain ⟨y, hy⟩ := Finite.exists_max (fun x : A × I => cost x.1 x.2)
  exact ⟨cost x.1 x.2, cost y.1 y.2, fun a i => ⟨hx (a, i), hy (a, i)⟩⟩

omit [Nonempty A] [Nonempty I] in
