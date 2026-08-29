import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma wt_insert_of_notMem {V : Finset X} {x : X} (hx : x ∉ V) {A : Finset X} (hA : A ⊆ V)
    (p : ℝ) : wt (insert x V) p A = (1 - p) * wt V p A := by
  have hxA : x ∉ A := fun h => hx (hA h)
  have : (insert x V) \ A = insert x (V \ A) := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨(rfl | hy), hy2⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hy, hy2⟩
    · rintro (rfl | ⟨hy, hy2⟩)
      · exact ⟨Or.inl rfl, hxA⟩
      · exact ⟨Or.inr hy, hy2⟩
  unfold wt
  rw [this, Finset.card_insert_of_notMem (by simp [hx]), pow_succ]
  ring

