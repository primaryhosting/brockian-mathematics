import Mathlib

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

import Mathlib

/-!
# Assembly Window Constants
Category: A Assembly
Target: Zeta23Scaffold.assembly_window_constants
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Scaffold

/-- The window function `H(λ) = 2 - 1/λ - λ/3`. -/
noncomputable def Hwin (lam : ℝ) : ℝ := 2 - 1 / lam - lam / 3

/-- The derived window constant `H_d(λ) = (1 + H(λ))/2`. -/
noncomputable def Hd (lam : ℝ) : ℝ := (1 + Hwin lam) / 2

/-- The window function `F(λ) = λ / (1 + λ²/3)`. -/
noncomputable def Fwin (lam : ℝ) : ℝ := lam / (1 + lam ^ 2 / 3)

/-- Window-constant assembly identities of preprint eq. (1.3):
`H(1) = 2/3`, `H_d(1) = 5/6`, `F(1) = 3/4`, and `2 F(1) - 1 = 1/2`. -/
theorem assembly_window_constants :
    Hwin 1 = 2 / 3 ∧ Hd 1 = 5 / 6 ∧ Fwin 1 = 3 / 4 ∧ 2 * Fwin 1 - 1 = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Hwin, Hd, Fwin] <;> norm_num

end Zeta23Scaffold

