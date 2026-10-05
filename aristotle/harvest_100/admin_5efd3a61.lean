import Mathlib

/-!
# Pigeonhole
Category: Frontier Wave 2 (deeper machinery)
Target: Combinatorics.pigeonhole
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

namespace Combinatorics

/-- **Pigeonhole principle.** If `f : s → t` is a map between finite types with
`Fintype.card t < Fintype.card s`, then `f` is not injective: there are distinct
`a b : s` with `f a = f b`. -/
theorem pigeonhole {s t : Type*} [Fintype s] [Fintype t] (f : s → t)
    (h : Fintype.card t < Fintype.card s) :
    (∃ a b : s, a ≠ b ∧ f a = f b) ∧ ¬ Function.Injective f := by
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt f h
  exact ⟨⟨a, b, hab, hfab⟩, fun hinj => hab (hinj hfab)⟩

end Combinatorics

