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

/-- A *Carmichael number*: a composite `n > 1` which is a Fermat pseudoprime to every base,
i.e. `n ∣ a ^ n - a` for all integers `a`. -/

theorem chernickNum_strictMono : StrictMono chernickNum := by
  intro a b hab
  unfold chernickNum
  have h12 : (6 * a + 1) * (12 * a + 1) < (6 * b + 1) * (12 * b + 1) := by nlinarith
  exact Nat.mul_lt_mul'' h12 (by omega)

/-- **Conditional infinitude of three-prime Carmichael numbers.**

The unconditional statement is an open problem; it would follow from Dickson's conjecture applied
to the Chernick triple `6k+1, 12k+1, 18k+1`.  Here we prove the reduction: *if* there are
infinitely many `k` for which `6k+1`, `12k+1` and `18k+1` are simultaneously prime, *then* there
are infinitely many Carmichael numbers with exactly three prime factors. -/
