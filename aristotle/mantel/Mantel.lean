import Mathlib
namespace Brockian.Mantel
/-- Mantel's theorem: a triangle-free graph on |V| vertices has at most ⌊|V|²/4⌋ edges. -/
theorem mantel {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.CliqueFree 3) :
    G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4 := by
  sorry
end Brockian.Mantel
