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

theorem isCarmichael_1729 : IsCarmichael 1729 ∧ (Nat.primeFactors 1729).card = 3 := by
  have := chernick_isCarmichael (k := 1) le_rfl (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- **Conditional infinitude of three-prime Carmichael numbers.**

Assuming the Dickson/Hardy–Littlewood-type hypothesis that the linear forms
`6k+1, 12k+1, 18k+1` are simultaneously prime for arbitrarily large `k`
(a special case of Dickson's conjecture, which is open), there are infinitely many
Carmichael numbers with exactly three prime factors. -/
