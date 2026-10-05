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

def NoSpareVariety (psi : D → R → Z) (z₀ : Z) : Prop :=
  ∀ d a b, psi d a = z₀ → psi d b = z₀ → a = b

/-- Contrapositive form of the base case: if the regulator makes a distinction that the system
itself does not make (`psi d = psi d'` but `r d ≠ r d'`), then either the regulator fails to
regulate, or the system does leave it spare variety. -/
