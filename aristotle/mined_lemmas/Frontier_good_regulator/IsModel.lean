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

def IsModel (psi : D → R → Z) (r : D → R) : Prop :=
  ∀ d d', psi d = psi d' → r d = r d'

/-- The system leaves the regulator *no unnecessary variety*: for each disturbance there is at
most one action achieving the target outcome. This is the deterministic base case of the
Conant–Ashby setting, in which an optimal regulator has no spare freedom in its choice of
action. -/
