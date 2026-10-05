import Mathlib
/-!
# Chinese Remainder
Category: Pure Mathematics
Target: Math.chinese_remainder
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

namespace Math

open scoped Function -- for the scoped `on` notation

/-- The canonical ring homomorphism `ZMod (∏ i, a i) →+* Π i, ZMod (a i)`, given componentwise
by reduction modulo `a i`. -/

theorem chineseRemainderHom_bijective {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) :
    Function.Bijective (chineseRemainderHom a) := by
  obtain ⟨e, he⟩ := chinese_remainder a coprime
  rw [← he]
  exact e.bijective

end Math

