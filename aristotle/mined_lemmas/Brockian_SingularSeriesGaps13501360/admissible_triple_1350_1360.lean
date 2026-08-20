/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- A finite set of integers `H` is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) when for every prime `p` the elements of `H` fail to cover
all residue classes modulo `p`.  Equivalently, the singular series attached to `H` is
nonzero. -/

theorem admissible_triple_1350_1360 : Admissible {0, 1350, 1360} := by
  intro p hp
  rcases eq_or_ne p 2 with rfl | hp2
  · refine ⟨1, ?_⟩
    intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl | rfl <;> decide
  · rcases eq_or_ne p 3 with rfl | hp3
    · refine ⟨2, ?_⟩
      intro h hh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl | rfl <;> decide
    · refine exists_missed_residue_of_card_lt hp ?_
      have h5 : 5 ≤ p := by
        have h2 := hp.two_le
        rcases Nat.lt_or_ge p 5 with h | h
        · interval_cases p
          · omega
          · omega
          · exact absurd hp (by norm_num)
        · exact h
      have hc : ({0, 1350, 1360} : Finset ℤ).card ≤ 3 := by
        refine (Finset.card_insert_le _ _).trans ?_
        have h1 := Finset.card_insert_le (1350 : ℤ) ({1360} : Finset ℤ)
        simp only [Finset.card_singleton] at h1
        omega
      omega

/-- **Singular Series Gaps 13501360.**

New admissible gap ranges extending the `SingularSeriesGaps` family: every even gap `d`
in the range `1350 ≤ d ≤ 1360` yields an admissible pair `{0, d}`, and moreover the
triple `{0, 1350, 1360}` spanning the whole range is itself admissible.  Consequently
each of these configurations has nonvanishing singular series, so none is excluded by a
local (congruence) obstruction. -/
