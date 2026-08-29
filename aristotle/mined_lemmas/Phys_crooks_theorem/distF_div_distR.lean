import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-!
## Setup

We model a driven thermodynamic experiment microscopically.

`Traj` is a (finite) set of microscopic trajectories of the *forward* protocol.
`rev` is the time-reversal involution sending a forward trajectory to the
corresponding trajectory of the *reverse* protocol, `work γ` is the work
performed on the system along `γ`, `probF` / `probR` are the probabilities of
the individual trajectories in the forward and reverse experiments,
`beta` is the inverse temperature and `deltaF` the free energy difference.

The single physical input is *microscopic reversibility* (generalized detailed
balance):

  `probF γ = exp (β (W γ - ΔF)) * probR (rev γ)`.

Crooks' fluctuation theorem is the statement that the same relation survives
coarse-graining, i.e. it holds for the *work distributions* obtained by summing
over all trajectories with a given value of the work.
-/

/-- A microscopically reversible driven-thermodynamics setup. -/
structure CrooksSystem (Traj : Type*) [Fintype Traj] where
  /-- Time reversal, mapping a forward trajectory to the reverse trajectory. -/
  rev : Traj → Traj
  /-- Time reversal is an involution. -/
  rev_involutive : Function.Involutive rev
  /-- Work performed on the system along a trajectory. -/
  work : Traj → ℝ
  /-- The work along a reversed trajectory is the negative of the original work. -/
  work_rev : ∀ γ, work (rev γ) = -work γ
  /-- Probability of a trajectory in the forward experiment. -/
  probF : Traj → ℝ
  /-- Probability of a trajectory in the reverse experiment. -/
  probR : Traj → ℝ
  /-- Inverse temperature. -/
  beta : ℝ
  /-- Free energy difference between the final and initial equilibrium states. -/
  deltaF : ℝ
  /-- Microscopic reversibility (generalized detailed balance). -/
  micro_rev : ∀ γ, probF γ = Real.exp (beta * (work γ - deltaF)) * probR (rev γ)

namespace CrooksSystem

variable {Traj : Type*} [Fintype Traj] (S : CrooksSystem Traj)

/-- The forward work distribution `P_F(w)`: total probability of forward
trajectories whose work equals `w`. -/

theorem distF_div_distR (w : ℝ) (h : S.distR (-w) ≠ 0) :
    S.distF w / S.distR (-w) = Real.exp (S.beta * (w - S.deltaF)) := by
  rw [S.distF_eq w, mul_div_assoc, div_self h, mul_one]

end CrooksSystem

/-- **Crooks fluctuation theorem.**

For a microscopically reversible driven thermodynamic system, the forward work
distribution `P_F` and the reverse work distribution `P_R` satisfy

  `P_F(W) / P_R(-W) = e^{β (W - ΔF)}`

for every value `W` of the work at which `P_R(-W) ≠ 0`; equivalently, and with
no nonvanishing hypothesis, `P_F(W) = e^{β (W - ΔF)} · P_R(-W)`. -/
