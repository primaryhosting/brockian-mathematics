/-
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
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

/-- A finite set of natural numbers is *admissible* when, for every prime `p`, its elements
omit at least one residue class modulo `p`.  This is exactly the classical condition under
which the singular series attached to the tuple is non-zero. -/

lemma isAdmissible_pair_of_even {d : ℕ} (hd : Even d) : IsAdmissible {0, d} := by
  intro p hp
  rcases eq_or_lt_of_le hp.two_le with h2 | h2
  · -- `p = 2`: both elements are even, so the residue `1` is omitted.
    subst h2
    refine ⟨1, ?_⟩
    intro h hh
    have hh2 : (2 : ℕ) ∣ h := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl
      · exact dvd_zero 2
      · exact hd.two_dvd
    have : (h : ZMod 2) = 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd h 2).mpr hh2
    rw [this]
    decide
  · obtain ⟨a, ha0, had⟩ := exists_avoided_residue_of_two_lt hp h2 0 d
    refine ⟨a, ?_⟩
    intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · exact ha0
    · exact had

/--
**Singular Series Gaps 1240–1250.**

For every gap value `d` in the range `1240 ≤ d ≤ 1250`, there exists an admissible tuple of
natural numbers of diameter exactly `d` — equivalently, a tuple whose singular series is
non-vanishing — if and only if `d` is even.  Thus the admissible gaps in this range are
exactly `1240, 1242, 1244, 1246, 1248, 1250`.
-/
