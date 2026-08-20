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

theorem IsAronszajnTree.bijOn_pred {T : Type*} [PartialOrder T] {lvl : T → Ordinal}
    (h : IsAronszajnTree T lvl) (x : T) : Set.BijOn lvl {y | y < x} (Set.Iio (lvl x)) := by
  refine ⟨fun y hy => h.lvl_strictMono hy, ?_, ?_⟩
  · intro y hy z hz hyz
    obtain ⟨w, -, hw⟩ := h.pred_unique x (lvl y) (h.lvl_strictMono hy)
    rw [hw y ⟨hy, rfl⟩, hw z ⟨hz, hyz.symm⟩]
  · intro b hb
    obtain ⟨y, ⟨hy, hyl⟩, -⟩ := h.pred_unique x b hb
    exact ⟨y, hy, hyl⟩

/-- **There exists an Aronszajn tree**: a tree of height `ω₁` all of whose levels are
countable and which has no uncountable branch (indeed no uncountable chain). -/
