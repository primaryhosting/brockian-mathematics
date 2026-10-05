/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxRecDepth 10000

namespace Math

private theorem key : ∀ b01 b02 b03 b04 b05 b12 b13 b14 b15 b23 b24 b25 b34 b35 b45 : Bool,
    (((b01 == b02) && (b02 == b12)) ||
    (((b01 == b03) && (b03 == b13)) ||
    (((b01 == b04) && (b04 == b14)) ||
    (((b01 == b05) && (b05 == b15)) ||
    (((b02 == b03) && (b03 == b23)) ||
    (((b02 == b04) && (b04 == b24)) ||
    (((b02 == b05) && (b05 == b25)) ||
    (((b03 == b04) && (b04 == b34)) ||
    (((b03 == b05) && (b05 == b35)) ||
    (((b04 == b05) && (b05 == b45)) ||
    (((b12 == b13) && (b13 == b23)) ||
    (((b12 == b14) && (b14 == b24)) ||
    (((b12 == b15) && (b15 == b25)) ||
    (((b13 == b14) && (b14 == b34)) ||
    (((b13 == b15) && (b15 == b35)) ||
    (((b14 == b15) && (b15 == b45)) ||
    (((b23 == b24) && (b24 == b34)) ||
    (((b23 == b25) && (b25 == b35)) ||
    (((b24 == b25) && (b25 == b45)) ||
    (((b34 == b35) && (b35 == b45)))))))))))))))))))))) = true := by decide

/-- Every 2-colouring of the edges of `K₆` contains a monochromatic triangle. -/
theorem ramsey6 (c : Sym2 (Fin 6) → Bool) :
    ∃ a b d : Fin 6, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
      c s(a, b) = c s(a, d) ∧ c s(a, d) = c s(b, d) := by
  have h := key (c s(0,1)) (c s(0,2)) (c s(0,3)) (c s(0,4)) (c s(0,5)) (c s(1,2)) (c s(1,3)) (c s(1,4)) (c s(1,5)) (c s(2,3)) (c s(2,4)) (c s(2,5)) (c s(3,4)) (c s(3,5)) (c s(4,5))
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact ⟨0, 1, 2, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨0, 1, 3, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨0, 1, 4, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨0, 1, 5, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨0, 2, 3, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨0, 2, 4, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨0, 2, 5, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨0, 3, 4, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨0, 3, 5, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨0, 4, 5, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨1, 2, 3, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨1, 2, 4, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨1, 2, 5, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨1, 3, 4, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨1, 3, 5, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨1, 4, 5, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨2, 3, 4, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨2, 3, 5, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨2, 4, 5, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨3, 4, 5, by decide, by decide, by decide, h.1, h.2⟩

/-- The "pentagon" 2-coloring of the edges of `K₅`: an edge is coloured `true`
exactly when its endpoints are consecutive modulo `5`. -/
def pentagonColoring : Sym2 (Fin 5) → Bool :=
  Sym2.lift ⟨fun i j => decide ((i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val),
    by intro i j; simp [or_comm]⟩

/-- The pentagon colouring of `K₅` has no monochromatic triangle. -/
theorem pentagonColoring_no_mono_triangle :
    ∀ a b d : Fin 5, a ≠ b → a ≠ d → b ≠ d →
      ¬(pentagonColoring s(a, b) = pentagonColoring s(a, d) ∧
        pentagonColoring s(a, d) = pentagonColoring s(b, d)) := by
  decide

/-- **R(3,3) = 6.**  Every 2-colouring of the edges of the complete graph `K₆`
contains a monochromatic triangle, while there is a 2-colouring of the edges of
`K₅` with no monochromatic triangle.  Edges are modelled as unordered pairs
`Sym2 (Fin n)`, and colours as `Bool`. -/
theorem ramsey_3_3 :
    (∀ c : Sym2 (Fin 6) → Bool, ∃ a b d : Fin 6, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
        c s(a, b) = c s(a, d) ∧ c s(a, d) = c s(b, d)) ∧
    (∃ c : Sym2 (Fin 5) → Bool, ∀ a b d : Fin 5, a ≠ b → a ≠ d → b ≠ d →
        ¬(c s(a, b) = c s(a, d) ∧ c s(a, d) = c s(b, d))) :=
  ⟨ramsey6, pentagonColoring, pentagonColoring_no_mono_triangle⟩

/-! ### Graph-theoretic form

The same result phrased with `SimpleGraph`: a monochromatic triangle for the
2-colouring "edge of `G`" / "non-edge of `G`" is a triangle of `G` or of its
complement. -/

/-- Every simple graph on six vertices contains three distinct vertices that are
pairwise adjacent or pairwise non-adjacent. -/
theorem ramsey6_graph (G : SimpleGraph (Fin 6)) :
    ∃ a b d : Fin 6, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
      ((G.Adj a b ∧ G.Adj a d ∧ G.Adj b d) ∨
        (¬ G.Adj a b ∧ ¬ G.Adj a d ∧ ¬ G.Adj b d)) := by
  classical
  obtain ⟨a, b, d, hab, had, hbd, h1, h2⟩ :=
    ramsey6 (Sym2.lift ⟨fun i j => decide (G.Adj i j), by intro i j; simp [G.adj_comm]⟩)
  simp only [Sym2.lift_mk, decide_eq_decide] at h1 h2
  refine ⟨a, b, d, hab, had, hbd, ?_⟩
  by_cases hx : G.Adj a b
  · exact Or.inl ⟨hx, h1.mp hx, h2.mp (h1.mp hx)⟩
  · exact Or.inr ⟨hx, fun hy => hx (h1.mpr hy), fun hy => hx (h1.mpr (h2.mpr hy))⟩

/-- The 5-cycle on the vertex set `Fin 5`. -/
def pentagonGraph : SimpleGraph (Fin 5) where
  Adj i j := (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val
  symm := by intro i j h; tauto
  loopless := ⟨by intro i; simp; omega⟩

instance : DecidableRel pentagonGraph.Adj := fun i j => by
  unfold pentagonGraph; infer_instance

/-- The 5-cycle has no triangle, and neither does its complement. -/
theorem pentagonGraph_no_mono_triangle :
    ∀ a b d : Fin 5, a ≠ b → a ≠ d → b ≠ d →
      ¬((pentagonGraph.Adj a b ∧ pentagonGraph.Adj a d ∧ pentagonGraph.Adj b d) ∨
        (¬ pentagonGraph.Adj a b ∧ ¬ pentagonGraph.Adj a d ∧ ¬ pentagonGraph.Adj b d)) := by
  decide

/-- **R(3,3) = 6**, graph-theoretic form: every simple graph on six vertices has
a triangle in itself or in its complement, and some simple graph on five
vertices (the 5-cycle) has neither. -/
theorem ramsey_3_3_graph :
    (∀ G : SimpleGraph (Fin 6), ∃ a b d : Fin 6, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
        ((G.Adj a b ∧ G.Adj a d ∧ G.Adj b d) ∨
          (¬ G.Adj a b ∧ ¬ G.Adj a d ∧ ¬ G.Adj b d))) ∧
    (∃ G : SimpleGraph (Fin 5), ∀ a b d : Fin 5, a ≠ b → a ≠ d → b ≠ d →
        ¬((G.Adj a b ∧ G.Adj a d ∧ G.Adj b d) ∨
          (¬ G.Adj a b ∧ ¬ G.Adj a d ∧ ¬ G.Adj b d))) :=
  ⟨ramsey6_graph, pentagonGraph, pentagonGraph_no_mono_triangle⟩

end Math

