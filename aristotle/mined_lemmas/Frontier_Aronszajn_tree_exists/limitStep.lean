import Mathlib
/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
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

open Set Cardinal Ordinal
open scoped Ordinal Cardinal

namespace Frontier

/-! ## Countable ordinals -/

/-- The set of ordinals below `a` is countable exactly when `a < ω₁`. -/

noncomputable def limitStep (l : Ordinal.{0}) (P : Ordinal.{0} → Ordinal.{0} → ℕ) :
    Ordinal.{0} → ℕ :=
  fun ξ => if ξ < l then max (P (cofSeq l (blockIdx l ξ)) ξ) (blockIdx l ξ) else 0

/-- `E a : Ordinal → ℕ` is (below `a`) a finite-to-one function, and the family `E` is
coherent: `E a` and `E b` agree on all but finitely many `ξ < b` whenever `b < a < ω₁`. -/
