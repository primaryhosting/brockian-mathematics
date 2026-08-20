/-
A Mathlib-facing restatement of `Frontier.arrow_impossibility`, with the finiteness of the
set of voters expressed by `Fintype` instead of by a list of voters covering everything.
-/
import Mathlib
import RequestProject.ArrowImpossibility

namespace Frontier

/-- **Arrow's impossibility theorem** for three alternatives and a finite set of voters:
no social welfare function is unanimous, independent of irrelevant alternatives and
non-dictatorial. -/

theorem rankFn_inj {x y z : Fin 3} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∀ a b, rankFn x y z a = rankFn x y z b → a = b := by
  revert hxy hxz hyz
  revert x y z
  decide

/-- The ranking `x ≻ y ≻ z`, for three distinct alternatives `x`, `y`, `z`. -/
