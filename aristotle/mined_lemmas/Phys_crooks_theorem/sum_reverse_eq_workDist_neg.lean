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

/-- The work distribution associated to a path measure `p` on a finite set of
microscopic trajectories `Γ`, with work functional `W`: the probability of
observing work value `w` is the total weight of the trajectories realizing it. -/

theorem sum_reverse_eq_workDist_neg {Γ : Type*} [Fintype Γ]
    (W : Γ → ℝ) (R : Γ → Γ) (hR : Function.Involutive R)
    (hW : ∀ γ, W (R γ) = -W γ) (pR : Γ → ℝ) (w : ℝ) :
    ∑ γ ∈ Finset.univ.filter (fun γ => W γ = w), pR (R γ) = workDist W pR (-w) := by
  unfold workDist
  refine Finset.sum_nbij' (i := R) (j := R) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [hW, ha]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    have := hW a
    rw [ha] at this
    simpa using this
  · intro a _; exact hR a
  · intro a _; exact hR a
  · intro a _; rfl

/-- **Crooks fluctuation theorem.**
Setting: a finite set `Γ` of microscopic trajectories, a time-reversal involution
`R : Γ → Γ` which flips the sign of the work `W`, forward and reverse path weights
`pF`, `pR`, inverse temperature `β` and free-energy difference `ΔF`, related by
microscopic reversibility `pF γ = e^{β (W γ - ΔF)} · pR (R γ)`.

Conclusion: the forward and reverse *work distributions* obey
`P_F(W) = e^{β (W - ΔF)} · P_R(-W)`, i.e. `P_F(W) / P_R(-W) = e^{β (W - ΔF)}`
whenever `P_R(-W) ≠ 0`. -/
