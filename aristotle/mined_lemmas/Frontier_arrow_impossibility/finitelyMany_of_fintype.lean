import Mathlib
import RequestProject.ArrowImpossibility

/-!
# Arrow impossibility, phrased with `Fintype`

`RequestProject.ArrowImpossibility` is deliberately self-contained (it uses no imports at
all), so it expresses finiteness of the voter set by `Frontier.FinitelyMany`.  This file
records the same statement with Mathlib's `Fintype` hypothesis.
-/

namespace Frontier

universe v


theorem finitelyMany_of_fintype {V : Type v} [Fintype V] : FinitelyMany V :=
  ⟨Finset.univ.toList, fun x => by simp⟩

/-- **Arrow's impossibility theorem** for three alternatives and a finite type of voters:
no social welfare function is unanimous, independent of irrelevant alternatives and
non-dictatorial. -/
