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

theorem crooksOfBoltzmann_micro_rev {Traj : Type*} [Fintype Traj]
    (rev : Traj → Traj) (rev_involutive : Function.Involutive rev)
    (Estart Eend : Traj → ℝ)
    (Estart_rev : ∀ γ, Estart (rev γ) = Eend γ)
    (Eend_rev : ∀ γ, Eend (rev γ) = Estart γ)
    (pathWeight : Traj → ℝ)
    (pathWeight_rev : ∀ γ, pathWeight (rev γ) = pathWeight γ)
    (beta deltaF Z₀ Z₁ : ℝ) (hZ₁ : Z₁ ≠ 0)
    (hΔF : Real.exp (-(beta * deltaF)) = Z₁ / Z₀) (γ : Traj) :
    Real.exp (-(beta * Estart γ)) / Z₀ * pathWeight γ
      = Real.exp (beta * ((Eend γ - Estart γ) - deltaF)) *
        (Real.exp (-(beta * Estart (rev γ))) / Z₁ * pathWeight (rev γ)) :=
  (crooksOfBoltzmann rev rev_involutive Estart Eend Estart_rev Eend_rev
    pathWeight pathWeight_rev beta deltaF Z₀ Z₁ hZ₁ hΔF).micro_rev γ

/-!
## A concrete instance

A two-trajectory example, showing that the hypotheses are satisfiable with a
genuinely non-degenerate work distribution (in particular `crooks_theorem` is
not vacuous).
-/

/-- A two-trajectory Crooks system: `true` is a trajectory with work `+1`,
`false` its time reverse, with work `-1`; inverse temperature `1` and zero free
energy difference. -/
