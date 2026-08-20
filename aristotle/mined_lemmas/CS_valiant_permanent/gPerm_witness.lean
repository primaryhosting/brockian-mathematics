import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed directly after the `import` line: Lean 4 requires `import`
commands to come first in a file.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

open Matrix

/-! ## Permanents as counting problems -/

/-- The permanent, written as a sum over permutations of the products `∏ i, M i (σ i)`
(Mathlib's definition uses `∏ i, M (σ i) i`; the two agree). -/

theorem gPerm_witness (v : Vtx W) : gadget W v (gPerm W τ c v) = 1 := by
  classical
  cases v with
  | inl i => simp [gPerm_apply, gFun, gIdx]
  | inr s =>
    rw [gPerm_apply]
    simp only [gFun, Sum.elim_inr]
    by_cases hs : s = gIdx W τ c s.1.1
    · rw [if_pos hs]; simp
    · rw [if_neg hs]; simp

/-- Every cycle cover of the gadget arises from a permutation `τ` together with a choice of one
parallel fresh vertex for each `i`. -/
