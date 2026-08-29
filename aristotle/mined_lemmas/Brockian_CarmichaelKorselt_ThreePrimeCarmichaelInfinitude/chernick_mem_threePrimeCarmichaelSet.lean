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
-/

set_option maxHeartbeats 1000000

namespace Brockian.CarmichaelKorselt

/-- A Carmichael number: a composite `n > 1` which is a Fermat pseudoprime to every base
coprime to it. -/

theorem chernick_mem_threePrimeCarmichaelSet {k : ℕ} (hk : 0 < k)
    (hp : Nat.Prime (6 * k + 1)) (hq : Nat.Prime (12 * k + 1)) (hr : Nat.Prime (18 * k + 1)) :
    (6 * k + 1) * (12 * k + 1) * (18 * k + 1) ∈ ThreePrimeCarmichaelSet := by
  have hprod : (6 * k + 1) * (12 * k + 1) * (18 * k + 1)
      = 36 * k * (36 * k ^ 2 + 11 * k + 1) + 1 := by ring
  have hsub : (6 * k + 1) * (12 * k + 1) * (18 * k + 1) - 1
      = 36 * k * (36 * k ^ 2 + 11 * k + 1) := by omega
  have hcar : IsCarmichael ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)) := by
    refine isCarmichael_of_three_primes hp hq hr (by omega) (by omega) (by omega) ?_ ?_ ?_ <;>
      rw [hsub]
    · exact ⟨6 * (36 * k ^ 2 + 11 * k + 1), by simp only [Nat.add_sub_cancel]; ring⟩
    · exact ⟨3 * (36 * k ^ 2 + 11 * k + 1), by simp only [Nat.add_sub_cancel]; ring⟩
    · exact ⟨2 * (36 * k ^ 2 + 11 * k + 1), by simp only [Nat.add_sub_cancel]; ring⟩
  exact ⟨hcar, _, _, _, hp, hq, hr, by omega, by omega, rfl⟩

/-- Unconditionally, `561 = 3 * 11 * 17` is a Carmichael number with three prime factors. -/
