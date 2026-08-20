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


theorem twoProfile_other {R1 R2 : Ranking (Fin 3)} {p j : V} (h : j ≠ p) :
    twoProfile R1 R2 p j = R2 := by
  simp [twoProfile, h]

end Profiles

/-! ## Arrow's theorem for three alternatives -/

section Arrow

variable {V : Type v} {F : (V → Ranking (Fin 3)) → Ranking (Fin 3)}

/-- If every voter puts `b` at the top or at the bottom, society cannot rank `b` strictly
between `a` and `c`. -/
