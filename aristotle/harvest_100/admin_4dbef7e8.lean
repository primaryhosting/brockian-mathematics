/-
# Quadratic Reciprocity
Category: Pure Mathematics
Target: Math.quadratic_reciprocity
Verification: verified (axiom-clean: propext, Classical.choice, Quot.sound)
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- **Quadratic reciprocity.** For distinct odd primes `p` and `q`,
`(p/q) * (q/p) = (-1) ^ (((p-1)/2) * ((q-1)/2))`, where `(a/n)` denotes the Legendre symbol.

This is a restatement of Mathlib's `legendreSym.quadratic_reciprocity`, with the exponent
written in the classical form `((p-1)/2) * ((q-1)/2)` (natural subtraction and division). -/
theorem quadratic_reciprocity {p q : ℕ} [Fact (Nat.Prime p)] [Fact (Nat.Prime q)]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q (p : ℤ) * legendreSym p (q : ℤ) = (-1) ^ (((p - 1) / 2) * ((q - 1) / 2)) := by
  have hp2 : (p - 1) / 2 = p / 2 := by
    have hodd : p % 2 = 1 := by
      rcases (Nat.Prime.eq_two_or_odd (Fact.out : Nat.Prime p)) with h | h
      · exact absurd h hp
      · exact h
    omega
  have hq2 : (q - 1) / 2 = q / 2 := by
    have hodd : q % 2 = 1 := by
      rcases (Nat.Prime.eq_two_or_odd (Fact.out : Nat.Prime q)) with h | h
      · exact absurd h hq
      · exact h
    omega
  rw [hp2, hq2]
  exact legendreSym.quadratic_reciprocity hp hq hpq

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

