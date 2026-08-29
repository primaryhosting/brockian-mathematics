/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment and is repeated below as the module docstring.)

import Mathlib

/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-! ## Graphs presented by neighbour maps -/

variable {n D k : ℕ}

/-- `walk nbr v w j` is the vertex reached from `v` after following the first `j`
directions of the direction sequence `w` in the `D`-regular graph given by the
neighbour map `nbr`. -/

theorem reach_iff_reflTransGen [NeZero D] (nbr : Fin n → Fin D → Fin n) (s t : Fin n) :
    Reach nbr s t ↔ Relation.ReflTransGen (fun u v => ∃ e, nbr u e = v) s t := by
  constructor
  · rintro ⟨w, j, rfl⟩
    induction j with
    | zero => exact Relation.ReflTransGen.refl
    | succ j ih => exact ih.tail ⟨w j, rfl⟩
  · intro h
    induction h with
    | refl => exact ⟨fun _ => (0 : Fin D), 0, rfl⟩
    | tail hu he ih =>
        obtain ⟨w, j, hw⟩ := ih
        obtain ⟨e, he⟩ := he
        refine ⟨Function.update w j e, j + 1, ?_⟩
        have hj : walk nbr s (Function.update w j e) j = walk nbr s w j := by
          refine walk_congr _ _ _ _ _ (fun x hx => ?_)
          exact Function.update_of_ne (Nat.ne_of_lt hx) _ _
        simp only [walk, hj, hw, Function.update_self, he]

/-- The undirected simple graph underlying a neighbour map. -/
