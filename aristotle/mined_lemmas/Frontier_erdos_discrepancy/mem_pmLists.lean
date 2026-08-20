import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib
import RequestProject.ErdosDiscrepancySpecialCases
import RequestProject.ErdosDiscrepancyMeasure

/-!
# The base case for completely multiplicative sequences

For a completely multiplicative `±1` sequence every homogeneous sum is `f d` times an
ordinary partial sum, so only the sums `S n = f 1 + ⋯ + f n` matter.  Tracking the four
values `f 2, f 3, f 5, f 7` shows that one of `S 4, S 6, S 8, S 10` must exceed `1` in
absolute value: for completely multiplicative sequences the length `10` already forces
discrepancy `2` (as opposed to `12` in general).
-/

namespace Frontier

/-- Unfolding the ordinary partial sums. -/

theorem mem_pmLists : ∀ L : List ℤ, (∀ x ∈ L, x = 1 ∨ x = -1) → L ∈ pmLists L.length := by
  intro L
  induction L with
  | nil => intro _; simp [pmLists]
  | cons x t ih =>
      intro h
      have ht : t ∈ pmLists t.length := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
      have hx : x = 1 ∨ x = -1 := h x (List.mem_cons_self ..)
      simp only [List.length_cons, pmLists, List.mem_flatMap]
      exact ⟨t, ht, by rcases hx with rfl | rfl <;> simp⟩

/-- The `±1` sequence read off from a pattern (index `k` uses the `(k-1)`-st entry). -/
