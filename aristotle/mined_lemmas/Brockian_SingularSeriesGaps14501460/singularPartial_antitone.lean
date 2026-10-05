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

lemma singularPartial_antitone :
    Antitone fun N => singularPartial gapTuple (N + 10) := by
  refine antitone_nat_of_succ_le fun n => ?_
  have hstep : singularPartial gapTuple (n + 10 + 1)
      = singularPartial gapTuple (n + 10)
        * (if (n + 10 + 1).Prime then localFactor gapTuple (n + 10 + 1) else 1) :=
    singularPartial_succ _ _
  have hpos := singularPartial_pos (n + 10)
  have hle : (if (n + 10 + 1).Prime then localFactor gapTuple (n + 10 + 1) else 1) ≤ 1 := by
    split_ifs with h
    · exact localFactor_le_one (by omega)
    · exact le_refl 1
  have hidx : n + 1 + 10 = n + 10 + 1 := by omega
  show singularPartial gapTuple (n + 1 + 10) ≤ singularPartial gapTuple (n + 10)
  rw [hidx, hstep]
  nlinarith [hpos, hle]

