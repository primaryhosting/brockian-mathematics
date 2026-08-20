import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem span_UU_eq_top {ζ : F} (hζ1 : ζ ≠ 1) :
    Submodule.span F (Set.range (UU ζ)) = (⊤ : Submodule F (Cube n → F)) := by
  classical
  refine top_le_iff.mp ?_
  rw [← (Pi.basisFun F (Cube n)).span_eq]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨y, rfl⟩
  have : (Pi.basisFun F (Cube n)) y = (delta y : Cube n → F) := by
    funext x
    rw [delta_apply]
    simp [Pi.basisFun_apply, Pi.single_apply]
  rw [this]
  exact delta_mem_span hζ1 y

/-- **Smolensky's dimension bound.** -/
