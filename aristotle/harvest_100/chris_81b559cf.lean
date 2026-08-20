import Mathlib

/-!
# Quadratic Reciprocity
Category: Pure Mathematics
Target: Math.quadratic_reciprocity
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

/-- **The Law of Quadratic Reciprocity.**
For distinct odd primes `p` and `q`,
`(p/q) * (q/p) = (-1) ^ (((p-1)/2) * ((q-1)/2))`,
where `(a/n)` denotes the Legendre symbol `legendreSym n a`.

The proof is a direct application of Mathlib's
`legendreSym.quadratic_reciprocity`, stated there with the exponent `p / 2 * (q / 2)`,
which agrees with `(p-1)/2 * ((q-1)/2)` for odd `p`, `q`. -/
theorem quadratic_reciprocity (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  have hp₁ : p % 2 = 1 := (Nat.Prime.eq_two_or_odd (Fact.out (p := p.Prime))).resolve_left hp
  have hq₁ : q % 2 = 1 := (Nat.Prime.eq_two_or_odd (Fact.out (p := q.Prime))).resolve_left hq
  have ep : (p - 1) / 2 = p / 2 := by omega
  have eq' : (q - 1) / 2 = q / 2 := by omega
  rw [ep, eq']
  exact legendreSym.quadratic_reciprocity hp hq hpq

end Math

