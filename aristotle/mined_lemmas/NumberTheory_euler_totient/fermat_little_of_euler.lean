/-
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace NumberTheory

/-- **Euler's theorem**, unit-group form: for a unit `u` of `ZMod n`,
`u ^ Nat.totient n = 1`. -/

theorem fermat_little_of_euler {p a : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  have hcop : Nat.Coprime a p := ((Nat.Prime.coprime_iff_not_dvd hp).2 ha).symm
  simpa [Nat.totient_prime hp] using euler_totient_modEq hcop

end NumberTheory

import Mathlib

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

