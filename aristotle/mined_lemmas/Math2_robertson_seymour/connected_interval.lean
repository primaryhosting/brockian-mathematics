import Mathlib

/-!
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON THE HEADER: Lean 4 requires `import` to be the first command of a file, so the
module docstring above is placed directly after `import Mathlib` (a `/-! ... -/` block
before the import is a parse error).
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Math2

universe u v w

open SimpleGraph

/-! ## The minor relation -/

/-- `IsMinor H G` says that `H` is a minor of `G`: there is a family of pairwise disjoint,
nonempty, connected *branch sets* `B w ⊆ V(G)`, indexed by the vertices `w` of `H`, such
that adjacent vertices of `H` have an edge of `G` between their branch sets. -/

theorem connected_interval {l : List Comp} {i a b : ℕ} (hi : i < l.length)
    (hab : a ≤ b) (hb : b < (compAt l i).size) :
    ((Forest l).induce {q : ForestVerts l | q.1.1 = i ∧ a ≤ q.1.2 ∧ q.1.2 ≤ b}).Connected := by
  set S : Set (ForestVerts l) := {q | q.1.1 = i ∧ a ≤ q.1.2 ∧ q.1.2 ≤ b} with hS
  have hlt : ∀ y : ℕ, y ≤ b → y < (compAt l i).size := fun y hy => lt_of_le_of_lt hy hb
  let v : ∀ y : ℕ, a ≤ y → y ≤ b → ↥S := fun y h1 h2 =>
    ⟨⟨(i, y), hi, hlt y h2⟩, rfl, h1, h2⟩
  haveI : Nonempty ↥S := ⟨v a le_rfl hab⟩
  refine SimpleGraph.Connected.mk ?_
  have key : ∀ y (h1 : a ≤ y) (h2 : y ≤ b),
      ((Forest l).induce S).Reachable (v a le_rfl hab) (v y h1 h2) := by
    intro y h1
    induction y, h1 using Nat.le_induction with
    | base => intro h2; exact SimpleGraph.Reachable.refl _
    | succ y hy ih =>
      intro h2
      have hstep : ((Forest l).induce S).Adj (v y hy (by omega)) (v (y + 1) (by omega) h2) :=
        ⟨rfl, Comp.adj_succ _ (hlt (y + 1) h2)⟩
      exact (ih (by omega)).trans hstep.reachable
  rintro ⟨⟨⟨i', x⟩, hx1, hx2⟩, hxS⟩ ⟨⟨⟨j', y⟩, hy1, hy2⟩, hyS⟩
  obtain ⟨hi', hax, hxb⟩ := hxS
  obtain ⟨hj', hay, hyb⟩ := hyS
  simp only at hi' hj'
  subst hi'
  subst hj'
  exact (key x hax hxb).symm.trans (key y hay hyb)

/-! ## Branch sets realizing a component as a minor of a larger component -/

/-- Lower endpoint of the branch set of position `x` of `c` inside `d`. -/
