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

theorem counting_diverges_of_discrete_and_WeylLawMatch {S : Set ℝ} {C d : ℝ}
    (hC : 0 < C) (hd : 0 < d) (hdisc : IsDiscreteSpectrum S) (hweyl : WeylLawMatch S C d) :
    Tendsto (fun t : ℝ => (spectralCounting S t : ℝ)) atTop atTop ∧ S.Infinite ∧ ¬ BddAbove S := by
  have hdiv := counting_tendsto_atTop_of_WeylLawMatch hC hd hweyl
  have hinf := infinite_of_counting_tendsto_atTop hdiv
  refine ⟨hdiv, hinf, ?_⟩
  rintro ⟨b, hb⟩
  have hsub : S ⊆ S ∩ Set.Iic b := fun x hx => ⟨hx, hb hx⟩
  exact hinf ((hdisc b).subset hsub)

/-! ### Non-vacuity: the hypotheses are satisfiable

The spectrum `S = {0, 1, 2, ...} ⊆ ℝ` is discrete and matches the Weyl asymptotic
`N(t) ∼ 1 · t ^ (2 / 2)`, so the hypotheses of the theorem above are not vacuous. -/

/-- The natural numbers, viewed as a spectrum inside `ℝ`. -/
