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
noncomputable def distF (w : ℝ) : ℝ := ∑ γ : Traj, if S.work γ = w then S.probF γ else 0

/-- The reverse work distribution `P_R(w)`: total probability of reverse
trajectories whose work equals `w`. -/
noncomputable def distR (w : ℝ) : ℝ := ∑ γ : Traj, if S.work γ = w then S.probR γ else 0

/-- Time reversal as a permutation of the trajectory space. -/
noncomputable def revEquiv : Traj ≃ Traj := S.rev_involutive.toPerm

@[simp] lemma revEquiv_apply (γ : Traj) : S.revEquiv γ = S.rev γ := rfl

/-- Reindexing the reverse work distribution at `-w` by time reversal:
it equals the sum of the reverse probabilities of the reversals of the forward
trajectories of work `w`. -/
lemma distR_neg_eq (w : ℝ) :
    S.distR (-w) = ∑ γ : Traj, if S.work γ = w then S.probR (S.rev γ) else 0 := by
  classical
  rw [distR]
  rw [← Equiv.sum_comp S.revEquiv (fun γ => if S.work γ = -w then S.probR γ else 0)]
  refine Finset.sum_congr rfl ?_
  intro γ _
  simp only [revEquiv_apply, S.work_rev γ, neg_inj]

/-- **Crooks fluctuation theorem** (product form):
`P_F(W) = e^{β (W - ΔF)} · P_R(-W)`. -/
theorem distF_eq (w : ℝ) :
    S.distF w = Real.exp (S.beta * (w - S.deltaF)) * S.distR (-w) := by
  classical
  rw [S.distR_neg_eq w, Finset.mul_sum, distF]
  refine Finset.sum_congr rfl ?_
  intro γ _
  by_cases h : S.work γ = w
  · simp only [h, if_true]
    rw [S.micro_rev γ, h]
  · simp only [h, if_false, mul_zero]

/-- **Crooks fluctuation theorem** (ratio form):
`P_F(W) / P_R(-W) = e^{β (W - ΔF)}`, whenever the reverse distribution does not
vanish at `-W`. -/
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
theorem crooks_theorem {Traj : Type*} [Fintype Traj] (S : CrooksSystem Traj) (w : ℝ) :
    S.distF w = Real.exp (S.beta * (w - S.deltaF)) * S.distR (-w) ∧
      (S.distR (-w) ≠ 0 →
        S.distF w / S.distR (-w) = Real.exp (S.beta * (w - S.deltaF))) :=
  ⟨S.distF_eq w, fun h => S.distF_div_distR w h⟩
/-!
## Microscopic reversibility from Boltzmann statistics

To see that the hypothesis `micro_rev` is not vacuous, we derive it from the
standard microscopic picture.  For a trajectory `γ`, let `Estart γ` be the
energy of its initial microstate, measured with the Hamiltonian in force at the
initial time of its protocol, and `Eend γ` the energy of its final microstate,
measured with the Hamiltonian in force at the final time.  Time reversal swaps
the two endpoints *and* the two Hamiltonians, so

  `Estart (rev γ) = Eend γ`  and  `Eend (rev γ) = Estart γ`,

and the work done on the system along a thermally isolated trajectory is
`W γ = Eend γ - Estart γ`.

The forward experiment starts in equilibrium with the initial Hamiltonian
(partition function `Z₀`), the reverse experiment starts in equilibrium with the
final Hamiltonian (partition function `Z₁`), and the conditional path weight is
invariant under time reversal.  The free energy difference obeys
`e^{-β ΔF} = Z₁ / Z₀`.  Microscopic reversibility then follows.
-/

/-- Construction of a `CrooksSystem` from Boltzmann-distributed initial
conditions and a time-reversal-invariant path weight. -/
noncomputable def crooksOfBoltzmann {Traj : Type*} [Fintype Traj]
    (rev : Traj → Traj) (rev_involutive : Function.Involutive rev)
    (Estart Eend : Traj → ℝ)
    (Estart_rev : ∀ γ, Estart (rev γ) = Eend γ)
    (Eend_rev : ∀ γ, Eend (rev γ) = Estart γ)
    (pathWeight : Traj → ℝ)
    (pathWeight_rev : ∀ γ, pathWeight (rev γ) = pathWeight γ)
    (beta deltaF Z₀ Z₁ : ℝ) (hZ₁ : Z₁ ≠ 0)
    (hΔF : Real.exp (-(beta * deltaF)) = Z₁ / Z₀) :
    CrooksSystem Traj where
  rev := rev
  rev_involutive := rev_involutive
  work := fun γ => Eend γ - Estart γ
  work_rev := by
    intro γ
    rw [Eend_rev γ, Estart_rev γ]
    ring
  probF := fun γ => Real.exp (-(beta * Estart γ)) / Z₀ * pathWeight γ
  probR := fun γ => Real.exp (-(beta * Estart γ)) / Z₁ * pathWeight γ
  beta := beta
  deltaF := deltaF
  micro_rev := by
    intro γ
    simp only [Estart_rev γ, pathWeight_rev γ]
    have hsplit : beta * (Eend γ - Estart γ - deltaF)
        = -(beta * Estart γ) + beta * Eend γ + -(beta * deltaF) := by ring
    rw [hsplit, Real.exp_add, Real.exp_add, hΔF]
    have hbc : Real.exp (beta * Eend γ) * Real.exp (-(beta * Eend γ)) = 1 := by
      rw [← Real.exp_add]
      simp
    set a := Real.exp (-(beta * Estart γ))
    set b := Real.exp (beta * Eend γ)
    set c := Real.exp (-(beta * Eend γ))
    set p := pathWeight γ
    have hrw : a * b * (Z₁ / Z₀) * (c / Z₁ * p) = (b * c) * (a / Z₀ * p) * (Z₁ / Z₁) := by
      field_simp
    rw [hrw, hbc, div_self hZ₁]
    ring

/-- The Boltzmann construction indeed satisfies the microscopic reversibility
relation, so the hypotheses of `crooks_theorem` are consistent and physically
realized. -/
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
noncomputable def twoTraj : CrooksSystem Bool where
  rev := not
  rev_involutive := Bool.not_not
  work := fun b => if b then 1 else -1
  work_rev := by
    intro b
    cases b <;> norm_num
  probF := fun b => Real.exp (if b then 1 else -1)
  probR := fun _ => 1
  beta := 1
  deltaF := 0
  micro_rev := by
    intro b
    cases b <;> norm_num

example : twoTraj.distR (-1) = 1 := by
  simp only [CrooksSystem.distR, Fintype.sum_bool, twoTraj]
  norm_num

example : twoTraj.distF 1 = Real.exp 1 := by
  simp only [CrooksSystem.distF, Fintype.sum_bool, twoTraj]
  norm_num

end Phys

