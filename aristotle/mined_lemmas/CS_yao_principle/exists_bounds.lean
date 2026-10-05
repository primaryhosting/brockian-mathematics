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

lemma exists_bounds (c : A → I → ℝ) : ∃ m M : ℝ, ∀ a i, m ≤ c a i ∧ c a i ≤ M := by
  obtain ⟨z, hz⟩ := Finite.exists_min (fun z : A × I => c z.1 z.2)
  obtain ⟨w, hw⟩ := Finite.exists_max (fun z : A × I => c z.1 z.2)
  exact ⟨c z.1 z.2, c w.1 w.2, fun a i => ⟨hz (a, i), hw (a, i)⟩⟩

/-! ### Weak duality (the "easy" direction of Yao's principle) -/

omit [Nonempty A] [Nonempty I] in
/-- For any randomized algorithm `p` and any input distribution `q`, the distributional
complexity of `q` is at most the worst-case expected cost of `p`.  This is the direction of
Yao's principle used for proving randomized lower bounds. -/
