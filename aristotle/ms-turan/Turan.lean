import Mathlib
namespace Brockian.Turan
/-- Turán's theorem (integer form): a K_{r+1}-free graph satisfies 2r·|E| ≤ (r−1)·|V|². -/
theorem turan {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (hr : 0 < r) (h : G.CliqueFree (r + 1)) :
    2 * r * G.edgeFinset.card ≤ (r - 1) * (Fintype.card V) ^ 2 := by
  sorry
end Brockian.Turan
