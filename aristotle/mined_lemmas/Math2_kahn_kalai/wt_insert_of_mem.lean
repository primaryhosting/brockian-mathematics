import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma wt_insert_of_mem {V : Finset X} {x : X} (hx : x ∉ V) {A : Finset X} (hA : A ⊆ V)
    (p : ℝ) : wt (insert x V) p (insert x A) = p * wt V p A := by
  have hxA : x ∉ A := fun h => hx (hA h)
  have h1 : (insert x V) \ (insert x A) = V \ A := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
    constructor
    · rintro ⟨(rfl | hy), hy2, hy3⟩
      · exact absurd rfl hy2
      · exact ⟨hy, hy3⟩
    · rintro ⟨hy, hy2⟩
      refine ⟨Or.inr hy, ?_, hy2⟩
      rintro rfl
      exact hx hy
  unfold wt
  rw [h1, Finset.card_insert_of_notMem hxA, pow_succ]
  ring

