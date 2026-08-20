/-!
# Pigeonhole
Category: Frontier Wave 2 (deeper machinery)
Target: Combinatorics.pigeonhole
Statement: The pigeonhole principle: if f maps a finite type s into a finite type t with card t < card s, then f is not injective (there exist a b in s, a != b, with f a = f b). (Use Mathlib's Fintype.exists_ne_map_eq_of_card_lt.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
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

/-- **The pigeonhole principle.** If `f : s → t` maps a finite type `s` into a finite type `t`
with `Fintype.card t < Fintype.card s`, then `f` is not injective: there are `a b : s` with
`a ≠ b` and `f a = f b`. -/
theorem pigeonhole {s t : Type*} [Fintype s] [Fintype t] (f : s → t)
    (h : Fintype.card t < Fintype.card s) :
    ∃ a b : s, a ≠ b ∧ f a = f b := by
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt f h
  exact ⟨a, b, hab, hfab⟩

/-- Equivalent phrasing: under the same cardinality hypothesis, `f` is not injective. -/
theorem pigeonhole_not_injective {s t : Type*} [Fintype s] [Fintype t] (f : s → t)
    (h : Fintype.card t < Fintype.card s) :
    ¬ Function.Injective f := by
  intro hinj
  obtain ⟨a, b, hab, hfab⟩ := pigeonhole f h
  exact hab (hinj hfab)

end Combinatorics

