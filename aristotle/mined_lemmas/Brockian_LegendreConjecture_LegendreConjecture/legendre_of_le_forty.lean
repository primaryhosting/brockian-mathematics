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

theorem legendre_of_le_forty (n : Nat) (hn : 0 < n) (hn' : n ≤ 40) :
    ∃ p : Nat, IsPrimeNat p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := legendreWitness_spec n (by omega) hn
  exact ⟨legendreWitness n, h3, h1, h2⟩

end Brockian.LegendreConjecture

import Mathlib
import Brockian.LegendreConjecture

/-!
# Legendre Conjecture — Mathlib companion results

This module connects the self-contained development in `Brockian.LegendreConjecture`
with Mathlib:

* `IsPrimeNat_iff_prime` : the trial-division primality predicate used there agrees
  with Mathlib's `Nat.Prime`;
* `legendreStatement_iff` / `shortIntervalPrimeHypothesis_iff` : the statements
  restated with `Nat.Prime`;
* `exists_prime_between_sq_and_two_sq` : the unconditional weakening of Legendre's
  conjecture supplied by Bertrand's postulate.
-/

namespace Brockian.LegendreConjecture

