import Mathlib
-- (Lean 4 requires `import` commands to precede any module docstring, so the required
-- header comment is reproduced verbatim immediately below.)

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Ordinal Set Cardinal
open scoped Ordinal

namespace Aronszajn

/-! ## Countable ordinals -/

/-- An ordinal is countable (i.e. its set of predecessors is countable) iff it is `< ω₁`. -/

lemma cs_spec {α : Ordinal.{0}} (hα : α < ω₁) {ξ : Ordinal.{0}} (hξ : ξ < α) :
    ∃ n, Good α ξ n := by
  classical
  have hex : ∃ g : ℕ → Ordinal.{0}, ∀ η < α, ∃ n, η ≤ g n ∧ g n < α := by
    obtain ⟨g, hg⟩ := ((countable_Iio_iff α).2 hα).exists_eq_range ⟨ξ, hξ⟩
    refine ⟨g, fun η hη => ?_⟩
    have : η ∈ Set.range g := by rw [← hg]; exact hη
    obtain ⟨n, rfl⟩ := this
    exact ⟨n, le_rfl, hη⟩
  have : cs α = hex.choose := by rw [cs, dif_pos hex]
  obtain ⟨n, h1, h2⟩ := hex.choose_spec ξ hξ
  exact ⟨n, by rw [Good, this]; exact ⟨h1, h2⟩⟩

/-- The least `n` with `Good α ξ n`, if any. -/
