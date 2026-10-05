/-
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- A finite set of integers `H` (a *pattern*, or *gap tuple*) is **admissible** when for every
prime `p` the reductions of the elements of `H` modulo `p` miss at least one residue class.
This is exactly the condition under which every local factor `1 - ν_p(H)/p` of the
Hardy–Littlewood singular series `𝔖(H) = ∏_p (1 - ν_p(H)/p)(1 - 1/p)^{-|H|}` is nonzero. -/

theorem admissible_triple_1242_1250 : Admissible ({0, 1242, 1250} : Finset ℤ) := by
  intro p hp
  have hple := hp.two_le
  by_cases h5 : 5 ≤ p
  · refine exists_missed_residue_of_card_lt _ p hp ?_
    have hc : ({0, 1242, 1250} : Finset ℤ).card ≤ 3 := by
      refine (Finset.card_insert_le _ _).trans ?_
      have h2 : ({1250} : Finset ℤ).card ≤ 1 := by simp
      have h3 : ({1242, 1250} : Finset ℤ).card ≤ 2 :=
        (Finset.card_insert_le _ _).trans (by simp)
      omega
    omega
  · push_neg at h5
    interval_cases p
    · refine ⟨1, ?_⟩
      intro h hh
      fin_cases hh <;> · push_cast; decide
    · refine ⟨1, ?_⟩
      intro h hh
      fin_cases hh <;> · push_cast; decide
    · exact absurd hp (by norm_num)

end Brockian

