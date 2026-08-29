import Mathlib
-- (Lean 4 requires `import` lines to precede every other command, including module
-- docstrings, so the required header comment appears immediately below the import.)

/-!
# Quadratic Reciprocity
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- For an odd natural number `n`, `(n - 1) / 2 = n / 2` (natural subtraction and division). -/
theorem odd_nat_pred_div_two (n : ℕ) (hn : Odd n) : (n - 1) / 2 = n / 2 := by
  obtain ⟨k, rfl⟩ := hn
  omega

/-- **Gauss's law of quadratic reciprocity**: for distinct odd primes `p` and `q`,
`legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2))`. -/
theorem quadratic_reciprocity {p q : ℕ} [Fact (Nat.Prime p)] [Fact (Nat.Prime q)]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  have hpodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp
  have hqodd : Odd q := (Fact.out : Nat.Prime q).odd_of_ne_two hq
  rw [odd_nat_pred_div_two p hpodd, odd_nat_pred_div_two q hqodd, mul_comm (legendreSym p q)]
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

