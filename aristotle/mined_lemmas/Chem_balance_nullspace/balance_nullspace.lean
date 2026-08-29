/-
# Balance Nullspace
Category: Chemistry
Target: Chem.balance_nullspace
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Chem

/-! ## A ℚ-linear functional that is positive on a finite family of positive reals -/

/-- Given finitely many *positive* real numbers `x s`, there is a `ℚ`-linear functional
`f : ℝ →ₗ[ℚ] ℚ` which is positive on all of them.  (Such an `f` is a rational
"approximation of the identity" on the `ℚ`-span of the `x s`.) -/

theorem balance_nullspace {Elem Species : Type*} [Fintype Species]
    (R : Reaction Elem Species) :
    R.Balances ↔ ∃ n : Species → ℤ, (∀ s, 0 < n s) ∧ (R.stoich).mulVec n = 0 :=
  Matrix.exists_pos_int_nullVector_iff R.stoich

/-! ## A worked example: `2 H₂ + O₂ → 2 H₂O` -/

/-- The formation of water from hydrogen and oxygen.  The species are `H₂`, `O₂`, `H₂O`
(the first two being reactants), the elements are `H` and `O`. -/
