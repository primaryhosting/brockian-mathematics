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

theorem E_limit_apply {l ξ : Ordinal.{0}} (hl : Order.IsSuccLimit l) (hξ : ξ < l)
    (hc : cofSeq l (blockIdx l ξ) < l) :
    E l ξ = max (E (cofSeq l (blockIdx l ξ)) ξ) (blockIdx l ξ) := by
  rw [E_limit hl, limitStep, if_pos hξ, dif_pos hc]

/-! ## The invariant -/

/-- The invariant maintained by the recursion: `E a` vanishes outside `Iio a`, it is
finite-to-one on `Iio a`, and it coheres with all earlier `E b`. -/
