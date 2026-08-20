/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- A finite set of non-negative integers `H` is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuple conjecture) if for every prime `p` the elements of `H`
do not cover all residue classes modulo `p`.  Equivalently, the local factor of the
singular series `𝔖(H)` attached to `H` is non-zero at every prime. -/

theorem gap_range_zero_two_six_eight_twelve :
    ({0, 2, 6, 8, 12} : Finset ℕ).card = 5 ∧
      ({0, 2, 6, 8, 12} : Finset ℕ).max' ⟨0, by decide⟩ -
        ({0, 2, 6, 8, 12} : Finset ℕ).min' ⟨0, by decide⟩ = 12 := by
  constructor
  · decide
  · have hmax : ({0, 2, 6, 8, 12} : Finset ℕ).max' ⟨0, by decide⟩ = 12 := by
      apply le_antisymm
      · exact Finset.max'_le _ _ _ (by decide)
      · exact Finset.le_max' _ _ (by decide)
    have hmin : ({0, 2, 6, 8, 12} : Finset ℕ).min' ⟨0, by decide⟩ = 0 := Nat.le_zero.1
      (Finset.min'_le _ _ (by decide))
    rw [hmax, hmin]

/-- **Singular Series Gaps 16021610.**

`{0, 2, 6, 8, 12}` is an admissible `5`-tuple (every prime misses at least one residue
class), it has exactly `5` elements, and its gap range (diameter) is `12`. -/
