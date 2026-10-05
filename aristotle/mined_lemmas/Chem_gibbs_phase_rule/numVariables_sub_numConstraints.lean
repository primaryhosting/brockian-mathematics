import Mathlib

/-!
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Module

/-- Number of intensive state variables used to describe a system of `C` chemical
components distributed over `P` phases: temperature, pressure, and the `C` mole
fractions of each of the `P` phases. -/

theorem numVariables_sub_numConstraints (C P : ℕ) (hP : 1 ≤ P) :
    (numVariables C P : ℤ) - (numConstraints C P : ℤ) = (C : ℤ) - (P : ℤ) + 2 := by
  unfold numVariables numConstraints
  have h : ((P - 1 : ℕ) : ℤ) = (P : ℤ) - 1 := by
    push_cast [Nat.cast_sub hP]
    ring
  push_cast [h]
  ring

/-- **Gibbs phase rule.**

The intensive state of a system of `C` components in `P` phases is described by a point
of `ℝ ^ (2 + P·C)` (temperature, pressure, and the mole fractions), subject to a system
of `P + C·(P-1)` independent equilibrium constraints, encoded by a surjective linear map
`f` whose fibres are the admissible states.  The number of degrees of freedom is the
affine dimension of such a fibre, i.e. the dimension of `ker f`, and it equals
`F = C - P + 2`. -/
