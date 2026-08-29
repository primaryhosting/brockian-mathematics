import Mathlib
/-!
# Quadratic Reciprocity
Category: Pure Mathematics
Target: Math.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **The Law of Quadratic Reciprocity.**
For distinct odd primes `p` and `q`,
`(p / q) * (q / p) = (-1) ^ (((p - 1) / 2) * ((q - 1) / 2))`,
where `(· / ·)` denotes the Legendre symbol. -/
theorem quadratic_reciprocity {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : Odd p) (hq : Odd q) (hpq : p ≠ q) :
    legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  have hp2 : p ≠ 2 := by rintro rfl; simp [Nat.odd_iff] at hp
  have hq2 : q ≠ 2 := by rintro rfl; simp [Nat.odd_iff] at hq
  have hpo := Nat.odd_iff.mp hp
  have hqo := Nat.odd_iff.mp hq
  have e1 : (p - 1) / 2 = p / 2 := by omega
  have e2 : (q - 1) / 2 = q / 2 := by omega
  rw [e1, e2, mul_comm (legendreSym p q)]
  exact legendreSym.quadratic_reciprocity hp2 hq2 hpq

end Math

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

