/-
# Assembly Window Constants
Category: A Assembly
Target: Zeta23Scaffold.assembly_window_constants
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Assembly Window Constants
Category: A Assembly
Target: Zeta23Scaffold.assembly_window_constants
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

namespace Zeta23Scaffold

/-- The window function `H(λ) = 2 - 1/λ - λ/3` of preprint eq. (1.3). -/

theorem two_Fwin_one_sub_one : 2 * Fwin 1 - 1 = 1 / 2 := by
  rw [Fwin_one]; norm_num

/-- Window-constant assembly identities of preprint eq. (1.3):
`H(1) = 2/3`, `H_d(1) = 5/6`, `F(1) = 3/4`, and `2F(1) - 1 = 1/2`. -/
