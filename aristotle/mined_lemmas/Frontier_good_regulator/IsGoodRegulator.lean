/-!
# Good Regulator
Category: Frontier Mind
Target: Frontier.good_regulator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

variable {D : Type u} {R : Type v} {Z : Type w}

/-
A **system** is described by a response map `psi : D → R → Z`: when the disturbance
(system state) is `d` and the regulator emits the action `a`, the outcome is `psi d a`.
-/

/-- `r` is a *good regulator* for the system `psi` with respect to the target outcome `z₀`
if it always steers the outcome to `z₀`, i.e. regulation succeeds for every disturbance. -/

def IsGoodRegulator (psi : D → R → Z) (z₀ : Z) (r : D → R) : Prop :=
  ∀ d, psi d (r d) = z₀

/-- `r` *is a model of the system* `psi`: the action chosen by the regulator depends on the
disturbance only through the system's own response behaviour `psi d : R → Z`. Equivalently,
the regulator's mapping factors through the system (see `good_regulator`). -/
