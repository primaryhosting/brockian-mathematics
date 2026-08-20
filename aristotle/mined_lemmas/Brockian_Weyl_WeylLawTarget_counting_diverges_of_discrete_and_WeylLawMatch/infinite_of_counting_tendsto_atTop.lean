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
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set

namespace Brockian.Weyl.WeylLawTarget

/-- The spectral counting function of a set `S ⊆ ℝ` (thought of as the spectrum of an
operator, listed without multiplicity): `spectralCounting S t` is the number of spectral
points that are `≤ t`. -/

theorem infinite_of_counting_tendsto_atTop {S : Set ℝ}
    (h : Tendsto (fun t : ℝ => (spectralCounting S t : ℝ)) atTop atTop) : S.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  have hbound : ∀ t : ℝ, (spectralCounting S t : ℝ) ≤ (S.ncard : ℝ) := by
    intro t
    exact_mod_cast Set.ncard_le_ncard Set.inter_subset_left hfin
  obtain ⟨t, ht⟩ := (h.eventually_ge_atTop ((S.ncard : ℝ) + 1)).exists
  linarith [hbound t]

/--
**Weyl law forces a divergent, infinite, unbounded spectrum.**

If a spectrum `S ⊆ ℝ` is discrete (finitely many points below every threshold) and its
counting function matches the Weyl asymptotic `N(t) ∼ C · t ^ (d / 2)` with `C > 0` and
`d > 0`, then the counting function diverges to `+∞`, the spectrum is infinite, and it is
unbounded above.

The divergence and the infinitude already follow from the Weyl asymptotic alone; the
discreteness hypothesis named in the statement is what upgrades infinitude to
unboundedness above.
-/
