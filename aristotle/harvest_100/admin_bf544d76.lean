/-
# Nat Countable
Category: Frontier — Set Theory
Target: Infinity.nat_countable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- `ℕ` is a countable type. In Mathlib this is the instance `Nat.instCountable`,
obtained here from `Countable.of_equiv` along the identity equivalence. -/
theorem nat_countable_type : Countable ℕ :=
  Countable.of_equiv ℕ (Equiv.refl ℕ)

/-- `ℕ` is an infinite type. In Mathlib this is the instance `Nat.infinite`;
here it is derived from `Infinite.of_injective` with the identity map. -/
theorem nat_infinite_type : Infinite ℕ :=
  Infinite.of_injective (fun n : ℕ => n) Function.injective_id

/-- **The naturals are countably infinite**: `ℕ` is a `Countable` type and is `Infinite`. -/
theorem nat_countable : Countable ℕ ∧ Infinite ℕ :=
  ⟨nat_countable_type, nat_infinite_type⟩

end Infinity

#print axioms Infinity.nat_countable

