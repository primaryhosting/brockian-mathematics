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


theorem dictatorship_unanimous_and_IIA {V : Type v} (i : V) :
    Unanimous (fun P : V → Ranking (Fin 3) => P i) ∧
      IIA (fun P : V → Ranking (Fin 3) => P i) ∧
      IsDictator (fun P : V → Ranking (Fin 3) => P i) i :=
  ⟨fun _ _ _ h => h i, fun _ _ _ _ h => (h i).1, fun _ _ _ h => h⟩

/-- **Arrow's impossibility theorem** (base case: three alternatives, finitely many
voters). No social welfare function aggregating individual rankings of three
alternatives into a social ranking is simultaneously unanimous, independent of
irrelevant alternatives, and non-dictatorial. -/
