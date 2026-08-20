/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- A finite set of natural numbers is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuple conjecture: its singular series is nonzero) when,
for every prime `p`, the elements of the set miss at least one residue class mod `p`. -/

theorem admissible_pattern9098ext : Admissible pattern9098ext := by
  intro p hp
  by_cases hbig : 10 < p
  · exact exists_missing_residue_of_card_lt _ _ (by rw [card_pattern9098ext]; omega)
  · push_neg at hbig
    have h2 := hp.two_le
    interval_cases p
    · exact ⟨1, by norm_num, by decide⟩
    · exact ⟨1, by norm_num, by decide⟩
    · exact absurd hp (by decide)
    · exact ⟨4, by norm_num, by decide⟩
    · exact absurd hp (by decide)
    · exact ⟨3, by norm_num, by decide⟩
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)

/-- **Singular Series Gaps 9098, extended family.**  Every translate of the ten-element
gap pattern of diameter `32` is admissible, and it contains the nine-element pattern,
so the whole family of gap ranges obtained by translating either pattern has nonzero
singular series. -/
