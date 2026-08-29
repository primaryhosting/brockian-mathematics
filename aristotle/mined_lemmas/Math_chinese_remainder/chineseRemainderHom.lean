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

def chineseRemainderHom {ι : Type*} [Fintype ι] (a : ι → ℕ) :
    ZMod (∏ i, a i) →+* Π i, ZMod (a i) :=
  Pi.ringHom fun i =>
    ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) (ZMod (a i))

/-- **Chinese Remainder Theorem.** For a finite family of pairwise-coprime moduli `a i`, the
canonical reduction map `ZMod (∏ i, a i) → Π i, ZMod (a i)` is a ring isomorphism: there is a
ring equivalence `ZMod (∏ i, a i) ≃+* Π i, ZMod (a i)` whose underlying function is exactly
the canonical map. -/
