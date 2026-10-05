import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma sum_nested_eq (V : Finset X) (t : Finset X → Finset (Finset X))
    (ht : ∀ W ∈ V.powerset, t W ⊆ V.powerset) (F : Finset X → Finset X → ℝ) :
    ∑ W ∈ V.powerset, ∑ U ∈ t W, F W U
      = ∑ x ∈ (V.powerset ×ˢ V.powerset).filter (fun x => x.2 ∈ t x.1), F x.1 x.2 := by
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun W hW => ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun U _ => rfl)
  ext U
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨ht W hW h, h⟩, fun h => h.2⟩

/-- **Key Lemma** (Park–Pham).  With `δ` the density of one round, the expected cost of the
cover produced by that round is small. -/
