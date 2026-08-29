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

theorem Inv_of_lt_omega1 : ∀ a : Ordinal.{0}, a < ω₁ → Inv a := by
  intro a
  induction a using Ordinal.limitRecOn with
  | zero => exact fun _ => Inv_zero
  | succ a ih => exact fun ha => Inv_succ (ih (lt_of_le_of_lt (Order.le_succ a) ha))
  | limit l hl ih =>
      exact fun ha => Inv_limit hl (exists_cofSeq hl ha) (fun b hb => ih b hb (hb.trans ha))

end Frontier

