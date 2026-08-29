import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
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

/-- A finite set of integer offsets `H` is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuples conjecture) if for every prime `p` the reductions
of the elements of `H` modulo `p` miss at least one residue class.  This is exactly
the condition under which the singular series `𝔖(H)` is nonzero. -/

theorem isAdmissible_pair_of_even {g : ℤ} (hg : Even g) : IsAdmissible {0, g} := by
  classical
  intro p hp
  rcases eq_or_ne p 2 with rfl | hp2
  · refine ⟨1, ?_⟩
    intro h hh
    have hg2 : (g : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd g 2).mpr (by exact_mod_cast hg.two_dvd)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · simp
    · rw [hg2]
      exact zero_ne_one
  · haveI : Fact p.Prime := ⟨hp⟩
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hcard : ({0, g} : Finset ℤ).card < p :=
      lt_of_le_of_lt (Finset.card_insert_le _ _) (by
        simpa using lt_of_le_of_lt (by simp : (Finset.card {g} : ℕ) + 1 ≤ 2) (by omega))
    exact exists_missed_residue_of_card_lt hcard

/-- A pair `{0, g}` with `g` odd is not admissible: modulo `2` the two offsets already
cover both residue classes. -/
