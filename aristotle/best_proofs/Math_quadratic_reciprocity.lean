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

namespace Math

/-- **Quadratic reciprocity**: for distinct odd primes `p` and `q`,
`(p/q) * (q/p) = (-1) ^ (((p-1)/2) * ((q-1)/2))`, where `(· / ·)` denotes the
Legendre symbol. -/
theorem quadratic_reciprocity {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    legendreSym p q * legendreSym q p = (-1 : ℤ) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  have hp1 : p % 2 = 1 := (hp.out.eq_two_or_odd).resolve_left hp2
  have hq1 : q % 2 = 1 := (hq.out.eq_two_or_odd).resolve_left hq2
  have hpe : (p - 1) / 2 = p / 2 := by omega
  have hqe : (q - 1) / 2 = q / 2 := by omega
  rw [hpe, hqe, mul_comm (legendreSym p q)]
  exact legendreSym.quadratic_reciprocity hp2 hq2 hpq

end Math

#print axioms Math.quadratic_reciprocity

