import Mathlib
/-!
# Quadratic Reciprocity
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- For an odd natural number `p`, the expressions `(p - 1) / 2` and `p / 2` agree
(natural-number division). -/
lemma sub_one_div_two_eq_div_two {p : ℕ} (hp : p % 2 = 1) : (p - 1) / 2 = p / 2 := by
  omega

/-- **Gauss's Law of Quadratic Reciprocity**: for distinct odd primes `p` and `q`,
`(p / q) * (q / p) = (-1) ^ ((p-1)/2 * (q-1)/2)`, where `(· / ·)` denotes the
Legendre symbol. -/
theorem quadratic_reciprocity {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  have hp₁ : p % 2 = 1 := (Nat.Prime.eq_two_or_odd (Fact.out (p := p.Prime))).resolve_left hp
  have hq₁ : q % 2 = 1 := (Nat.Prime.eq_two_or_odd (Fact.out (p := q.Prime))).resolve_left hq
  rw [sub_one_div_two_eq_div_two hp₁, sub_one_div_two_eq_div_two hq₁,
    mul_comm (legendreSym p q) (legendreSym q p)]
  exact legendreSym.quadratic_reciprocity hp hq hpq

/- A concrete instance: `(5 / 13) * (13 / 5) = 1 = (-1) ^ (2 * 6)`. -/
section Example

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

example : legendreSym 5 13 * legendreSym 13 5 = (-1) ^ ((5 - 1) / 2 * ((13 - 1) / 2)) :=
  quadratic_reciprocity (by norm_num) (by norm_num) (by norm_num)

end Example

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

