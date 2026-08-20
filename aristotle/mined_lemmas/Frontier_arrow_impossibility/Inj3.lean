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


def Inj3 (r : Fin 3 → Nat) : Prop := ∀ x y : Fin 3, r x = r y → x = y

instance (r : Fin 3 → Nat) : Decidable (Inj3 r) := by
  unfold Inj3; infer_instance

/-- The ranking of the three alternatives that puts `a` first, `b` second and the
remaining alternative last (for `a ≠ b`). -/
