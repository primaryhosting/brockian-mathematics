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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open Finset

/-- `sigmaOne n` is the sum of all positive divisors of `n`. -/

theorem betrothedPairs_infinite_iff_firsts_infinite :
    betrothedPairs.Infinite ↔ betrothedFirsts.Infinite := by
  constructor
  · intro hinf
    have himg : (Prod.fst '' betrothedPairs).Infinite :=
      hinf.image injOn_fst_betrothedPairs
    refine himg.mono ?_
    rintro x ⟨⟨m, n⟩, hp, rfl⟩
    exact ⟨n, hp⟩
  · intro hinf hfin
    exact hinf (Set.Finite.subset (hfin.image Prod.fst) (by
      rintro m ⟨n, hb⟩
      exact ⟨(m, n), hb, rfl⟩))

/-- No number below `48` is the first member of a betrothed pair: together with
`isBetrothed_48_75`, this shows `(48, 75)` is the smallest betrothed pair. -/
