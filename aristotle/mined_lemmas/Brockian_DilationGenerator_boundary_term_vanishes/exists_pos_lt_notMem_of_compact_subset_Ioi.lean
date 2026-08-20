/-
# Boundary Term Vanishes
Category: Gate1 Operator
Target: Brockian.DilationGenerator.boundary_term_vanishes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Boundary Term Vanishes
Category: Gate1 Operator
Target: Brockian.DilationGenerator.boundary_term_vanishes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace DilationGenerator

open Filter Set Topology

/-- A compact subset of `(0, ∞)` is bounded away from `0`: there is `ε > 0` such that no
point below `ε` belongs to the set. -/

lemma exists_pos_lt_notMem_of_compact_subset_Ioi {S : Set ℝ} (hS : IsCompact S)
    (hsub : S ⊆ Set.Ioi (0 : ℝ)) : ∃ ε > (0 : ℝ), ∀ x < ε, x ∉ S := by
  rcases S.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, fun x _ => by simp [h]⟩
  · obtain ⟨a, haS, hmin⟩ := hS.exists_isMinOn h continuousOn_id
    refine ⟨a, hsub haS, fun x hx hxS => ?_⟩
    exact absurd (hmin hxS) (not_le.mpr hx)

/-- A compact set of reals is bounded above: there is `M` such that no point above `M`
belongs to the set. -/
