/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Ordinal Set Cardinal
open scoped Classical

namespace Frontier

/-- The first uncountable ordinal `ω₁`. -/

theorem enumIio_surj {a : Ordinal} (hc : (Set.Iio a).Countable) {x : Ordinal} (hx : x < a) :
    ∃ n, enumIio a n = x := by
  obtain ⟨g, hg⟩ := hc.exists_eq_range ⟨x, hx⟩
  have hex : ∃ g : ℕ → Ordinal, ∀ y < a, ∃ m, g m = y := by
    refine ⟨g, fun y hy => ?_⟩
    have : y ∈ Set.range g := by rw [← hg]; exact hy
    exact this
  obtain ⟨m, hm⟩ := hex.choose_spec x hx
  refine ⟨m, ?_⟩
  unfold enumIio
  rw [dif_pos hex, if_pos (by rw [hm]; exact hx)]
  exact hm

/-- A strictly increasing sequence, cofinal in `a` when `a` is a countable limit ordinal. -/
