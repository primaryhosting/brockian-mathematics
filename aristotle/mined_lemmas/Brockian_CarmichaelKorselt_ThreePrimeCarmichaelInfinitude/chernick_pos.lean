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

theorem chernick_pos {k : ℕ} (h : ChernickTriple k) : 0 < k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · exfalso; subst hk; have := h.1; norm_num at this
  · exact hk

/-- Chernick's theorem: if `6k+1`, `12k+1`, `18k+1` are all prime, then their product is a
Carmichael number. -/
