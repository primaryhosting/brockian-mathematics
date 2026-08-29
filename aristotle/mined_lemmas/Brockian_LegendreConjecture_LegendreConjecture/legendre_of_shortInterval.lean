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

import Brockian.LegendreConjectureExtras
#print axioms Brockian.LegendreConjecture.LegendreConjecture
#print axioms Brockian.LegendreConjecture.legendre_of_le_forty
#print axioms Brockian.LegendreConjecture.IsPrimeNat_iff_prime
#print axioms Brockian.LegendreConjecture.exists_prime_between_sq_and_two_sq
#print axioms Brockian.LegendreConjecture.legendre_of_shortInterval

/-!
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained (no `import` lines), so that the header
comment above can literally be the first thing in the file: Lean 4 requires all
`import` commands to precede every other piece of syntax except plain comments,
and a module doc comment `/-! ... -/` counts as syntax.

Mathlib-based companion results (in particular the identification of the
primality predicate used here with `Nat.Prime`, and Bertrand's postulate as an
unconditional partial result) live in `Brockian/LegendreConjectureExtras.lean`,
which imports this module.
-/

namespace Brockian.LegendreConjecture

/-- Primality of a natural number, spelled out by trial division:
`p` is prime iff `2 ≤ p` and no `d` with `2 ≤ d < p` divides `p`.
This is proved equivalent to Mathlib's `Nat.Prime` in
`Brockian/LegendreConjectureExtras.lean`. -/

theorem legendre_of_shortInterval
    (H : ∀ x m : ℕ, 0 < m → m ^ 2 ≤ x → ∃ p : ℕ, p.Prime ∧ x < p ∧ p ≤ x + m)
    (n : ℕ) (hn : 0 < n) : ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 :=
  legendreStatement_iff.mp
    (LegendreConjecture (shortIntervalPrimeHypothesis_iff.mpr H)) n hn

/-- **Unconditional partial result** (Bertrand's postulate): for every `n ≥ 1` there is a
prime `p` with `n ^ 2 < p ≤ 2 * n ^ 2`. -/
