import Mathlib

/-!
# Quadratic Reciprocity
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede any module docstring, so the
-- requested header block appears immediately after the single `import Mathlib` line.

namespace NumberTheory

/-- For an odd prime `p`, the natural-number division `(p - 1) / 2` agrees with `p / 2`. -/
lemma sub_one_div_two_eq_div_two_of_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (p - 1) / 2 = p / 2 := by
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  omega

/-- **Gauss's law of quadratic reciprocity**: for distinct odd primes `p` and `q`,
`legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2))`. -/
theorem quadratic_reciprocity {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  have hp' : p.Prime := Fact.out
  have hq' : q.Prime := Fact.out
  rw [sub_one_div_two_eq_div_two_of_odd_prime hp' hp,
    sub_one_div_two_eq_div_two_of_odd_prime hq' hq, mul_comm (legendreSym p q)]
  exact legendreSym.quadratic_reciprocity hp hq hpq

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

