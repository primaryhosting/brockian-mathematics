import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma Exp_mono {V : Finset X} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f g : Finset X → ℝ}
    (h : ∀ A ∈ V.powerset, f A ≤ g A) : Exp V p f ≤ Exp V p g := by
  unfold Exp
  refine Finset.sum_le_sum ?_
  intro A hA
  exact mul_le_mul_of_nonneg_left (h A hA) (wt_nonneg hp0 hp1 A)

