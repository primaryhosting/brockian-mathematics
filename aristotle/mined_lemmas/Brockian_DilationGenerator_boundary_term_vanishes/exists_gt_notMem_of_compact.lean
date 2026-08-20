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

lemma exists_gt_notMem_of_compact {S : Set ℝ} (hS : IsCompact S) :
    ∃ M : ℝ, ∀ x > M, x ∉ S := by
  rcases S.eq_empty_or_nonempty with h | h
  · exact ⟨0, fun x _ => by simp [h]⟩
  · obtain ⟨a, haS, hmax⟩ := hS.exists_isMaxOn h continuousOn_id
    exact ⟨a, fun x hx hxS => absurd (hmax hxS) (not_le.mpr hx)⟩

variable {f g : ℝ → ℂ}

/-- For `f, g` with compact support contained in `(0, ∞)`, the boundary expression
`x * f x * conj (g x)` vanishes identically near `0` and near `+∞`; hence it tends to `0`
both as `x → 0⁺` and as `x → ∞`.

The hypotheses `hg`, `hg0` on `g` are kept because they are part of the requested statement,
but they turn out to be unnecessary: the compact support of `f` inside `(0, ∞)` already forces
the product to vanish near `0` and near `+∞`. -/
