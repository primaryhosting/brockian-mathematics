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

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- A finite set of integer shifts `H` is *admissible* if for every prime `p` the
elements of `H` miss at least one residue class modulo `p`.  Equivalently, the
singular series `𝔖(H) = ∏_p (1 - ν_H(p)/p)(1 - 1/p)^{-|H|}` attached to `H` is
nonzero, which is the necessary local condition in the Hardy–Littlewood prime
`k`-tuple conjecture. -/

theorem admissible_octuplet :
    Admissible ({0, 2, 6, 8, 12, 18, 20, 26} : Finset ℤ) := by
  intro p hp
  by_cases hle : 8 < p
  · refine exists_missed_residue_of_card_lt _ p (by omega) ?_
    have : ({0, 2, 6, 8, 12, 18, 20, 26} : Finset ℤ).card = 8 := by decide
    omega
  · have h2 := hp.two_le
    interval_cases p <;> revert hp <;> decide

/-- **Singular Series Gaps 16021610.**  There is an admissible tuple of eight
integer shifts contained in the gap range `[0, 26]`, with both endpoints attained;
i.e. an admissible `8`-tuple of diameter `26`.  Admissibility means that for every
prime `p` some residue class mod `p` is missed, so the associated singular series
is nonzero and the Hardy–Littlewood conjecture predicts infinitely many prime
constellations with this gap pattern. -/
