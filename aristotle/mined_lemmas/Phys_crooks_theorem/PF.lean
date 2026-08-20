/-
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

/-- Data for a (discrete) nonequilibrium thermodynamic protocol together with its
time-reverse, in the setting of the Crooks fluctuation theorem.

`Traj` is the (finite) set of microscopic trajectories of the forward process,
`rev` is the time-reversal involution sending a forward trajectory to the
corresponding reverse trajectory, `work` is the work performed on the system along
a trajectory, `pF` and `pR` are the probabilities of a trajectory under the forward
and reverse protocol respectively, `beta` is the inverse temperature and `deltaF`
the free-energy difference between the two equilibrium end states.

The two physical inputs are:
* `work_rev`: the work along a reversed trajectory is minus the forward work;
* `microscopic_reversibility`: the detailed-balance / microscopic reversibility
  relation `pF γ = e^{β (W γ - ΔF)} · pR (rev γ)`.
-/
structure CrooksSetup (Traj : Type*) [Fintype Traj] [DecidableEq Traj] where
  /-- Time reversal of trajectories. -/
  rev : Traj → Traj
  /-- Time reversal is an involution. -/
  rev_involutive : Function.Involutive rev
  /-- Work performed along a trajectory. -/
  work : Traj → ℝ
  /-- Probability (weight) of a trajectory under the forward protocol. -/
  pF : Traj → ℝ
  /-- Probability (weight) of a trajectory under the reverse protocol. -/
  pR : Traj → ℝ
  /-- Inverse temperature. -/
  beta : ℝ
  /-- Free energy difference. -/
  deltaF : ℝ
  /-- The work along the reversed trajectory is the negative of the forward work. -/
  work_rev : ∀ γ, work (rev γ) = -work γ
  /-- Microscopic reversibility (detailed balance). -/
  microscopic_reversibility :
    ∀ γ, pF γ = Real.exp (beta * (work γ - deltaF)) * pR (rev γ)

namespace CrooksSetup

variable {Traj : Type*} [Fintype Traj] [DecidableEq Traj] (S : CrooksSetup Traj)

/-- The forward work distribution: the total probability of forward trajectories
whose work equals `w`. -/

noncomputable def PF (w : ℝ) : ℝ :=
  ∑ γ ∈ Finset.univ.filter (fun γ => S.work γ = w), S.pF γ

/-- The reverse work distribution: the total probability, under the reverse protocol,
of the trajectories whose work equals `w`. -/
