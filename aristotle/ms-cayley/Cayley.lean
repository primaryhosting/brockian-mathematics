import Mathlib
namespace Brockian.Cayley
/-- Cayley's formula: the number of labeled trees on n ≥ 1 vertices is n^(n−2)
    (counted as spanning trees of the complete graph, i.e. connected acyclic simple graphs). -/
theorem cayley_formula (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card {G : SimpleGraph (Fin n) // G.IsTree} = n ^ (n - 2) := by
  sorry
end Brockian.Cayley
