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

lemma singularPartial_tendsto :
    ∃ L : ℝ, 0 < L ∧ Filter.Tendsto (singularPartial gapTuple) Filter.atTop (nhds L) := by
  have hanti := singularPartial_antitone
  have hbdd : BddBelow (Set.range fun N => singularPartial gapTuple (N + 10)) := by
    refine ⟨1 / 2100, ?_⟩
    rintro x ⟨N, rfl⟩
    exact singularPartial_ge _
  have h := tendsto_atTop_ciInf hanti hbdd
  refine ⟨⨅ N, singularPartial gapTuple (N + 10), ?_, ?_⟩
  · have : (1:ℝ) / 2100 ≤ ⨅ N, singularPartial gapTuple (N + 10) :=
      le_ciInf fun N => singularPartial_ge _
    linarith
  · exact (Filter.tendsto_add_atTop_iff_nat 10).mp h

/-! ## Minimality of the diameter -/

/-- No admissible 4-tuple fits into a window of seven consecutive integers: the diameter `8`
realised by `gapTuple` is the least possible one for an admissible 4-tuple. -/
