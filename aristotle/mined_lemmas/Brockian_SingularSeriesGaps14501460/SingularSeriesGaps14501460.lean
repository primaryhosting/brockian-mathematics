import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Brockian

/-- The gap window: the integers of the range `[1450, 1460]`. -/

theorem SingularSeriesGaps14501460 :
    gapTuple = {1451, 1453, 1457, 1459} ∧
    gapTuple.card = 4 ∧
    (∀ h ∈ gapTuple, (1450 : ℤ) ≤ h ∧ h ≤ 1460) ∧
    (∀ a ∈ gapTuple, ∀ b ∈ gapTuple, b - a ≤ 8) ∧
    (∃ a ∈ gapTuple, ∃ b ∈ gapTuple, b - a = 8) ∧
    Admissible gapTuple ∧
    (∀ N, 0 < singularPartial gapTuple N) ∧
    (∀ N, (1 : ℝ) / 2100 ≤ singularPartial gapTuple N) ∧
    (∀ (K : Finset ℤ) (c : ℤ), K ⊆ Finset.Icc c (c + 6) → K.card = 4 → ¬ Admissible K) ∧
    ∃ L : ℝ, 0 < L ∧ Filter.Tendsto (singularPartial gapTuple) Filter.atTop (nhds L) := by
  refine ⟨gapTuple_eq, gapTuple_card, ?_, ?_, ?_, gapTuple_admissible, singularPartial_pos,
    singularPartial_ge, no_admissible_four_short, singularPartial_tendsto⟩
  · intro h hh
    obtain ⟨h1, h2⟩ := gapTuple_bounds h hh
    omega
  · intro a ha b hb
    obtain ⟨-, h2⟩ := gapTuple_bounds b hb
    obtain ⟨h3, -⟩ := gapTuple_bounds a ha
    omega
  · exact ⟨1451, by rw [gapTuple_eq]; decide, 1459, by rw [gapTuple_eq]; decide, by norm_num⟩

end Brockian

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

