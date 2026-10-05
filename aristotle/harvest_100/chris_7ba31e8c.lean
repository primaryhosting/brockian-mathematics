import Mathlib

/-!
# Nat Countable
Category: Frontier — Set Theory
Target: Infinity.nat_countable
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

/-- `Nat` is countable: the identity map is an injection into `Nat`. -/
theorem nat_countable_aux : Countable Nat :=
  Countable.mk ⟨id, Function.injective_id⟩

/-- `Nat` is infinite: if it were a `Fintype`, the supremum `N` of all its elements
would satisfy `N + 1 ≤ N`, a contradiction. -/
theorem nat_infinite_aux : Infinite Nat :=
  ⟨fun h => by
    have hle : ∀ m : Nat, m ≤ (Finset.univ : Finset Nat).sup id := fun m =>
      Finset.le_sup (f := id) (Finset.mem_univ m)
    exact absurd (hle ((Finset.univ : Finset Nat).sup id + 1)) (by omega)⟩

/-- The naturals are countably infinite: `Nat` is a `Countable` type and is `Infinite`. -/
theorem nat_countable : Countable Nat ∧ Infinite Nat :=
  ⟨nat_countable_aux, nat_infinite_aux⟩

end Infinity

