/-
# Quadratic Reciprocity
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: the header above is written as a plain block comment (`/- -/`) rather than a
-- module docstring (`/-! -/`), because Lean 4 rejects a module docstring that appears
-- before the `import` commands. The text is otherwise exactly as requested.

import Mathlib

namespace NumberTheory

/-- **Gauss's law of quadratic reciprocity**: for distinct odd primes `p` and `q`,
`legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2))`,
where the exponent is computed with natural number subtraction and division. -/

theorem quadratic_reciprocity {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  have hp1 : p % 2 = 1 := (Fact.out (p := p.Prime)).eq_two_or_odd.resolve_left hp2
  have hq1 : q % 2 = 1 := (Fact.out (p := q.Prime)).eq_two_or_odd.resolve_left hq2
  have hpe : (p - 1) / 2 = p / 2 := by omega
  have hqe : (q - 1) / 2 = q / 2 := by omega
  rw [hpe, hqe, mul_comm (legendreSym p q)]
  exact legendreSym.quadratic_reciprocity hp2 hq2 hpq

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

