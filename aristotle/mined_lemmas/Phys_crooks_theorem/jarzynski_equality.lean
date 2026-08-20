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

theorem jarzynski_equality {Traj : Type*} [Fintype Traj] [DecidableEq Traj]
    (S : CrooksSetup Traj) (hnorm : ∑ γ, S.pR γ = 1) :
    ∑ γ, S.pF γ * Real.exp (-S.beta * S.work γ) = Real.exp (-S.beta * S.deltaF) := by
  have key : ∀ γ : Traj, S.pF γ * Real.exp (-S.beta * S.work γ)
      = Real.exp (-S.beta * S.deltaF) * S.pR (S.rev γ) := by
    intro γ
    rw [S.microscopic_reversibility γ,
      mul_comm (Real.exp (S.beta * (S.work γ - S.deltaF))) (S.pR (S.rev γ)),
      mul_assoc, ← Real.exp_add,
      mul_comm (Real.exp (-S.beta * S.deltaF)) (S.pR (S.rev γ))]
    ring_nf
  rw [Finset.sum_congr rfl (fun γ _ => key γ), ← Finset.mul_sum,
    Fintype.sum_bijective S.rev S.rev_involutive.bijective _ S.pR (fun _ => rfl), hnorm,
    mul_one]

/-- A concrete two-trajectory setup showing that the hypotheses of `crooks_theorem`
are satisfiable with a nonzero reverse work distribution. -/
