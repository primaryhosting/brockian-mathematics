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

namespace Brockian
namespace CarmichaelKorselt

/-- Korselt's criterion, used here as the definition of a Carmichael number:
`n` is composite (`1 < n` and not prime), squarefree, and `p - 1 ∣ n - 1` for every
prime `p` dividing `n`. -/

theorem chernick_isCarmichael (hk : 1 ≤ k)
    (h1 : Nat.Prime (6 * k + 1)) (h2 : Nat.Prime (12 * k + 1)) (h3 : Nat.Prime (18 * k + 1)) :
    IsCarmichael ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)) ∧
      ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)).primeFactors.card = 3 := by
  have hexp := chernick_expand k
  have hsub : (6 * k + 1) * (12 * k + 1) * (18 * k + 1) - 1
      = 36 * k * (36 * k ^ 2 + 11 * k + 1) := by omega
  refine isCarmichael_three_primes h1 h2 h3 (by omega) (by omega) (by omega) ?_ ?_ ?_ <;>
    rw [hsub]
  · exact ⟨6 * (36 * k ^ 2 + 11 * k + 1), by simp; ring⟩
  · exact ⟨3 * (36 * k ^ 2 + 11 * k + 1), by simp; ring⟩
  · exact ⟨2 * (36 * k ^ 2 + 11 * k + 1), by simp; ring⟩

end Chernick

/-- `1729` (the Hardy–Ramanujan number, `k = 1` in Chernick's family) is a Carmichael
number with exactly three prime factors. -/
