import Mathlib

/-!
# Rationals Countable
Category: Frontier — Set Theory
Target: Infinity.rationals_countable
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

namespace Infinity

/-- There is an explicit bijection `ℕ ≃ ℚ`; equivalently, `ℚ` is denumerable. -/
noncomputable def natEquivRat : ℕ ≃ ℚ := Denumerable.eqv ℚ |>.symm

/-- `ℚ` is infinite, so no bijection with a finite type exists; combined with countability
this pins down its cardinality as `ℵ₀`. -/
theorem rat_infinite : Infinite ℚ := inferInstance

/-- **The rationals are countable.**
We record this in three equivalent forms: `Countable ℚ`, the existence of an injection
`ℚ ↪ ℕ`, and the cardinal equality `#ℚ = ℵ₀`. -/
theorem rationals_countable :
    Countable ℚ ∧ (∃ f : ℚ → ℕ, Function.Injective f) ∧ Cardinal.mk ℚ = Cardinal.aleph0 := by
  refine ⟨inferInstance, ⟨Encodable.encode, Encodable.encode_injective⟩, ?_⟩
  exact Cardinal.mkRat

end Infinity

