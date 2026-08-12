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
noncomputable def PR (w : ℝ) : ℝ :=
  ∑ γ ∈ Finset.univ.filter (fun γ => S.work γ = w), S.pR γ

/-- Time reversal is a bijection from the trajectories of work `-w` onto the
trajectories of work `w`; consequently the reverse work distribution at `-w` is the
sum of `pR (rev γ)` over the trajectories `γ` of work `w`. -/
theorem PR_neg (w : ℝ) :
    S.PR (-w) = ∑ γ ∈ Finset.univ.filter (fun γ => S.work γ = w), S.pR (S.rev γ) := by
  unfold PR
  refine Finset.sum_nbij' (fun γ => S.rev γ) (fun γ => S.rev γ) ?_ ?_ ?_ ?_ ?_ <;>
    intro γ hγ <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S.work_rev,
      S.rev_involutive γ] at hγ ⊢
  · rw [hγ, neg_neg]
  · rw [hγ]

/-- **Crooks fluctuation theorem** (unnormalized form):
`P_F(W) = e^{β (W - ΔF)} · P_R(-W)`. -/
theorem crooks_mul (w : ℝ) :
    S.PF w = Real.exp (S.beta * (w - S.deltaF)) * S.PR (-w) := by
  rw [PR_neg, PF, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro γ hγ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
  rw [S.microscopic_reversibility γ, hγ]

end CrooksSetup

/-- **Crooks fluctuation theorem**: for a discrete nonequilibrium protocol satisfying
microscopic reversibility, the ratio of the forward work distribution at `W` to the
reverse work distribution at `-W` is `e^{β (W - ΔF)}`. -/
theorem crooks_theorem {Traj : Type*} [Fintype Traj] [DecidableEq Traj]
    (S : CrooksSetup Traj) (w : ℝ) (hw : S.PR (-w) ≠ 0) :
    S.PF w / S.PR (-w) = Real.exp (S.beta * (w - S.deltaF)) := by
  rw [S.crooks_mul w, mul_div_assoc, div_self hw, mul_one]

/-- **Jarzynski equality**, a consequence of microscopic reversibility: if the reverse
process is normalized, then the forward average of `e^{-β W}` is `e^{-β ΔF}`. -/
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
noncomputable def twoStateSetup (beta deltaF : ℝ) : CrooksSetup Bool where
  rev := not
  rev_involutive := Bool.not_not
  work := fun b => if b then 1 else -1
  pF := fun b => if b then Real.exp (beta * (1 - deltaF)) else Real.exp (beta * (-1 - deltaF))
  pR := fun _ => 1
  beta := beta
  deltaF := deltaF
  work_rev := by intro b; cases b <;> norm_num
  microscopic_reversibility := by intro b; cases b <;> simp

example (beta deltaF : ℝ) :
    (twoStateSetup beta deltaF).PF 1 / (twoStateSetup beta deltaF).PR (-1)
      = Real.exp (beta * (1 - deltaF)) := by
  refine crooks_theorem _ 1 ?_
  simp [CrooksSetup.PR, twoStateSetup]

end Phys

