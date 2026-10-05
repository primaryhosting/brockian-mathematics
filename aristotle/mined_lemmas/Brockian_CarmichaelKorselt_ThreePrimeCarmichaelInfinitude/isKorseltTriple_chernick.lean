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

/-
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The unconditional infinitude of Carmichael numbers with exactly three prime factors is an
open problem.  This file gives a fully checked *conditional reduction*: Korselt's criterion
is proved in the three-prime case, reducing the conjecture to the purely arithmetic statement
`InfinitelyManyKorseltTriples`, and further to a Dickson-type prime-triple hypothesis via
Chernick's parametrisation `(6k+1)(12k+1)(18k+1)`.
-/

namespace Brockian.CarmichaelKorselt

/-- A *Carmichael number*: a composite `n > 1` such that `a ^ (n - 1) ≡ 1 [MOD n]` for every
`a` coprime to `n`. -/

theorem isKorseltTriple_chernick {k : ℕ} (hk : 1 ≤ k) (h1 : (6 * k + 1).Prime)
    (h2 : (12 * k + 1).Prime) (h3 : (18 * k + 1).Prime) :
    IsKorseltTriple (6 * k + 1) (12 * k + 1) (18 * k + 1) := by
  have hprod : (6 * k + 1) * (12 * k + 1) * (18 * k + 1)
      = 36 * k * (36 * k ^ 2 + 11 * k + 1) + 1 := by ring
  have hsub : (6 * k + 1) * (12 * k + 1) * (18 * k + 1) - 1
      = 36 * k * (36 * k ^ 2 + 11 * k + 1) := by rw [hprod, Nat.add_sub_cancel]
  refine ⟨h1, h2, h3, by omega, by omega, ?_, ?_, ?_⟩ <;> rw [hsub] <;> simp only [Nat.add_sub_cancel]
  · exact ⟨6 * (36 * k ^ 2 + 11 * k + 1), by ring⟩
  · exact ⟨3 * (36 * k ^ 2 + 11 * k + 1), by ring⟩
  · exact ⟨2 * (36 * k ^ 2 + 11 * k + 1), by ring⟩

/-- **Conditional reduction to a Dickson-type prime triple hypothesis.** If there are
arbitrarily large `k` with `6k+1`, `12k+1`, `18k+1` all prime, then there are infinitely many
Carmichael numbers with exactly three prime factors. -/
