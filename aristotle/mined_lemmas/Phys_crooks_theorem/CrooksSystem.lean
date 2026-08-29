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

/--
A discrete model of a driven thermodynamic system used to state the Crooks
fluctuation theorem.

* `Γ` is the (finite) set of microscopic trajectories of the forward protocol.
* `rev` is the time-reversal (conjugation) involution sending a forward
  trajectory to the corresponding trajectory of the reverse protocol.
* `work γ` is the work performed on the system along the trajectory `γ`.
* `pF` / `pR` are the path probabilities under the forward / reverse protocol.
* `beta` is the inverse temperature and `deltaF` the free-energy difference.

The two physical inputs are:

* `work_rev`  : the work is odd under time reversal, `W(γ̄) = -W(γ)`;
* `microscopic_reversibility` : the detailed-balance / microscopic reversibility
  relation `p_F(γ) = e^{β (W(γ) - ΔF)} p_R(γ̄)`.
-/
structure CrooksSystem (Γ : Type*) [Fintype Γ] where
  /-- Time reversal of trajectories. -/
  rev : Γ ≃ Γ
  /-- Work performed along a trajectory. -/
  work : Γ → ℝ
  /-- Path probability under the forward protocol. -/
  pF : Γ → ℝ
  /-- Path probability under the reverse protocol. -/
  pR : Γ → ℝ
  /-- Inverse temperature. -/
  beta : ℝ
  /-- Free energy difference between the two equilibrium end states. -/
  deltaF : ℝ
  /-- The work is odd under time reversal. -/
  work_rev : ∀ γ, work (rev γ) = -work γ
  /-- Microscopic reversibility. -/
  microscopic_reversibility :
    ∀ γ, pF γ = Real.exp (beta * (work γ - deltaF)) * pR (rev γ)

variable {Γ : Type*} [Fintype Γ]

/-- The forward work distribution `P_F(W)`: total probability of forward
trajectories whose work equals `w`. -/

theorem CrooksSystem.crooks_mul (S : CrooksSystem Γ) (w : ℝ) :
    S.PF w = Real.exp (S.beta * (w - S.deltaF)) * S.PR (-w) := by
  classical
  have key : S.PF w
      = ∑ γ : Γ, Real.exp (S.beta * (w - S.deltaF)) *
          (if S.work γ = w then S.pR (S.rev γ) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro γ _
    by_cases hγ : S.work γ = w
    · rw [if_pos hγ, if_pos hγ, S.microscopic_reversibility γ, hγ]
    · simp [hγ]
  rw [key, ← Finset.mul_sum, S.sum_pR_rev w]

/-- **Crooks fluctuation theorem**.

For a driven system satisfying microscopic reversibility, the ratio of the
forward work distribution at `W` to the reverse work distribution at `-W` is
`e^{β (W - ΔF)}`:
`P_F(W) / P_R(-W) = e^{β (W - ΔF)}`,
valid whenever the reverse distribution does not vanish; equivalently, in the
always-valid product form `P_F(W) = e^{β (W - ΔF)} P_R(-W)`. -/
