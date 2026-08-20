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

import Mathlib
import Brockian.RieselCovering

/-!
# Riesel Problem — Mathlib interface

Companion to `Brockian.RieselCovering` (which is import-free): the same result phrased with
Mathlib's `Nat.Prime`.
-/

namespace Brockian
namespace RieselCovering

/-- `509203 * 2 ^ n - 1` is not prime for any `n ≥ 1`, stated with `Nat.Prime`. -/

theorem not_nat_prime (n : ℕ) (hn : 1 ≤ n) : ¬ Nat.Prime (509203 * 2 ^ n - 1) := by
  intro hp
  obtain ⟨d, h1, h2, h3⟩ := RieselProblem n hn
  rcases hp.eq_one_or_self_of_dvd d h3 with h | h <;> omega

end RieselCovering
end Brockian

/-!
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
A *Riesel number* is an odd `k` such that `k * 2 ^ n - 1` is composite for every `n ≥ 1`.
This file exhibits Riesel's original witness `k = 509203` together with the covering
congruence argument that proves it, and derives that `509203 * 2 ^ n - 1` is composite
for all `n ≥ 1`.

The argument.  Each of the primes `3, 5, 7, 13, 17, 241` divides
`2 ^ 24 - 1 = 16777215 = 3 ^ 2 * 5 * 7 * 13 * 17 * 241`, so modulo each of them the powers
of two are periodic with period dividing `24`.  A direct finite check shows that for every
residue `r < 24` one of these primes divides `509203 * 2 ^ r - 1`; the table is recorded in
`Brockian.RieselCovering.coveringTable`.  Periodicity (`dvd_shift`, `dvd_shift_iter`) then
propagates each of these divisibilities to all `n` congruent to `r` modulo `24`.

The file is deliberately self-contained: it uses no imports, so all arithmetic facts are
proved from Lean core (`decide`, `omega`) only.
-/

namespace Brockian
namespace RieselCovering

/-- Riesel's witness `k = 509203`. -/
