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
noncomputable def CrooksSystem.PF (S : CrooksSystem Γ) (w : ℝ) : ℝ :=
  ∑ γ : Γ, if S.work γ = w then S.pF γ else 0

/-- The reverse work distribution `P_R(W)`: total probability of reverse
trajectories whose work equals `w`. -/
noncomputable def CrooksSystem.PR (S : CrooksSystem Γ) (w : ℝ) : ℝ :=
  ∑ γ : Γ, if S.work γ = w then S.pR γ else 0

/-- Reindexing along the time-reversal involution: summing `p_R ∘ rev` over the
forward trajectories of work `w` gives the reverse-protocol weight of work `-w`. -/
theorem CrooksSystem.sum_pR_rev (S : CrooksSystem Γ) (w : ℝ) :
    (∑ γ : Γ, if S.work γ = w then S.pR (S.rev γ) else 0) = S.PR (-w) := by
  classical
  have h : ∀ γ : Γ,
      (if S.work γ = w then S.pR (S.rev γ) else 0)
        = (fun δ : Γ => if S.work δ = -w then S.pR δ else 0) (S.rev γ) := by
    intro γ
    simp only [S.work_rev γ, neg_inj]
  rw [Finset.sum_congr rfl (fun γ _ => h γ)]
  exact Equiv.sum_comp S.rev (fun δ : Γ => if S.work δ = -w then S.pR δ else 0)

/-- Crooks fluctuation theorem, product form:
`P_F(W) = e^{β (W - ΔF)} · P_R(-W)`. -/
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
theorem crooks_theorem (S : CrooksSystem Γ) (w : ℝ) :
    S.PF w = Real.exp (S.beta * (w - S.deltaF)) * S.PR (-w) ∧
      (S.PR (-w) ≠ 0 → S.PF w / S.PR (-w) = Real.exp (S.beta * (w - S.deltaF))) := by
  refine ⟨S.crooks_mul w, ?_⟩
  intro h
  rw [S.crooks_mul w, mul_div_assoc, div_self h, mul_one]

/-! ### Non-vacuity: the hypotheses are satisfiable by a nondegenerate system -/

/-- A concrete two-trajectory system satisfying all the hypotheses, with strictly
positive path probabilities. This shows `crooks_theorem` is not vacuous. -/
noncomputable def twoStateSystem (beta deltaF w₀ : ℝ) : CrooksSystem Bool where
  rev := ⟨not, not, fun b => by cases b <;> rfl, fun b => by cases b <;> rfl⟩
  work := fun b => if b then w₀ else -w₀
  pF := fun b => Real.exp (beta * ((if b then w₀ else -w₀) - deltaF)) * (1 / 2)
  pR := fun _ => 1 / 2
  beta := beta
  deltaF := deltaF
  work_rev := by intro b; cases b <;> simp
  microscopic_reversibility := by intro b; cases b <;> rfl

example (beta deltaF w₀ : ℝ) (b : Bool) : 0 < (twoStateSystem beta deltaF w₀).pF b := by
  have : (twoStateSystem beta deltaF w₀).pF b
      = Real.exp (beta * ((if b then w₀ else -w₀) - deltaF)) * (1 / 2) := rfl
  rw [this]
  positivity

#print axioms Phys.crooks_theorem

end Phys

