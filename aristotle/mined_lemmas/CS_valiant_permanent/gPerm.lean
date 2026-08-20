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

noncomputable def gPerm : Equiv.Perm (Vtx W) :=
  Equiv.ofBijective (gFun W τ c) (Finite.injective_iff_bijective.1 (gFun_injective W τ c))

