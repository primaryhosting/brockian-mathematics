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
