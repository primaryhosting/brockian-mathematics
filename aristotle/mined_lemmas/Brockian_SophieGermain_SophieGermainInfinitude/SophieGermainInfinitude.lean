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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- `p` is a *Sophie Germain prime* if both `p` and `2 * p + 1` are prime. -/

theorem SophieGermainInfinitude (hD : DicksonsConjecture) :
    {p : ℕ | IsSophieGermain p}.Infinite := by
  rw [show {p : ℕ | IsSophieGermain p} = sophieGermainSet from rfl,
    infinite_sophieGermainSet_iff_unbounded]
  intro N
  obtain ⟨n, hn, hprime⟩ := hD 2 sgForms sgForms_pos admissible_sgForms N
  refine ⟨n, hn, ?_, ?_⟩
  · have := hprime 0
    simpa [sgForms] using this
  · have := hprime 1
    simpa [sgForms] using this

/-! ## Unconditional partial results -/

/-- Explicit small Sophie Germain primes. -/
