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

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace CarmichaelKorselt

/-- A *Carmichael number*: a composite `n > 1` which is a Fermat pseudoprime to every base,
i.e. `a ^ n ≡ a [MOD n]` for all `a`. -/

theorem isCarmichael_chernick {k : ℕ} (hk : 1 ≤ k) (h6 : (6 * k + 1).Prime)
    (h12 : (12 * k + 1).Prime) (h18 : (18 * k + 1).Prime) :
    IsCarmichael ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)) := by
  have hprod : (6 * k + 1) * (12 * k + 1) * (18 * k + 1)
      = 1296 * k ^ 3 + 396 * k ^ 2 + 36 * k + 1 := by ring
  have hsub : (6 * k + 1) * (12 * k + 1) * (18 * k + 1) - 1
      = 1296 * k ^ 3 + 396 * k ^ 2 + 36 * k := by omega
  refine isCarmichael_of_korselt h6 h12 h18 (by omega) (by omega) ?_ ?_ ?_
  · refine ⟨216 * k ^ 2 + 66 * k + 6, ?_⟩
    rw [hsub]; simp only [Nat.add_sub_cancel]; ring
  · refine ⟨108 * k ^ 2 + 33 * k + 3, ?_⟩
    rw [hsub]; simp only [Nat.add_sub_cancel]; ring
  · refine ⟨72 * k ^ 2 + 22 * k + 2, ?_⟩
    rw [hsub]; simp only [Nat.add_sub_cancel]; ring

/-- The set of Carmichael numbers that are a product of three distinct primes. -/
