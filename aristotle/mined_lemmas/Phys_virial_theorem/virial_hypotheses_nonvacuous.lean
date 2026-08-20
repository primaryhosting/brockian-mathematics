/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Statement: For a bound stationary state, 2⟨T⟩ = ⟨r·∇V⟩ (quantum virial theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Filter Topology

namespace Phys

/-- **Auxiliary integration-by-parts fact.**  If `f` is everywhere differentiable with
integrable derivative `f'` and `f` tends to `0` at both ends of the real line, then the
integral of `f'` over `ℝ` vanishes. -/

theorem virial_hypotheses_nonvacuous :
    (∀ x, HasDerivAt hoPsi (hoDPsi x) x) ∧
    (∀ x, HasDerivAt hoDPsi (hoDDPsi x) x) ∧
    (∀ x, HasDerivAt hoV (hoDV x) x) ∧
    (∀ x, -hoDDPsi x + hoV x * hoPsi x = 1 * hoPsi x) ∧
    Integrable (fun x => hoDPsi x ^ 2) volume ∧
    Integrable (fun x => hoPsi x ^ 2) volume ∧
    Integrable (fun x => hoV x * hoPsi x ^ 2) volume ∧
    Integrable (fun x => x * hoDV x * hoPsi x ^ 2) volume ∧
    Tendsto (fun x => hoPsi x * hoDPsi x) atBot (𝓝 0) ∧
    Tendsto (fun x => hoPsi x * hoDPsi x) atTop (𝓝 0) ∧
    Tendsto (fun x => x * (hoDPsi x ^ 2 + (1 - hoV x) * hoPsi x ^ 2)) atBot (𝓝 0) ∧
    Tendsto (fun x => x * (hoDPsi x ^ 2 + (1 - hoV x) * hoPsi x ^ 2)) atTop (𝓝 0) ∧
    hoPsi ≠ 0 := by
  have hdsq : ∀ x : ℝ, hoDPsi x ^ 2 = x ^ 2 * Real.exp (-x ^ 2) := by
    intro x
    have hx : hoDPsi x = -x * hoPsi x := rfl
    rw [hx, mul_pow, hoPsi_sq]
    ring
  have hcur : ∀ x : ℝ, hoPsi x * hoDPsi x = -(x * Real.exp (-x ^ 2)) := by
    intro x
    have hx : hoDPsi x = -x * hoPsi x := rfl
    rw [hx, show hoPsi x * (-x * hoPsi x) = -(x * hoPsi x ^ 2) by ring, hoPsi_sq]
  have hPhi : ∀ x : ℝ, x * (hoDPsi x ^ 2 + (1 - hoV x) * hoPsi x ^ 2)
      = x * Real.exp (-x ^ 2) := by
    intro x
    rw [hdsq, hoPsi_sq, hoV]
    ring
  refine ⟨hasDerivAt_hoPsi, hasDerivAt_hoDPsi, hasDerivAt_hoV, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro x; rw [hoDDPsi, hoV, hoPsi]; ring
  · exact (integrable_congr (Filter.Eventually.of_forall hdsq)).2 integrable_sq_mul_exp_neg_sq
  · exact (integrable_congr (Filter.Eventually.of_forall hoPsi_sq)).2 integrable_exp_neg_sq
  · refine (integrable_congr (Filter.Eventually.of_forall (fun x => ?_))).2
      integrable_sq_mul_exp_neg_sq
    rw [hoV, hoPsi_sq]
  · refine (integrable_congr (Filter.Eventually.of_forall (fun x => ?_))).2
      (integrable_sq_mul_exp_neg_sq.const_mul 2)
    rw [hoDV, hoPsi_sq]; ring
  · simpa [hcur] using tendsto_mul_exp_neg_sq_atBot.neg
  · simpa [hcur] using tendsto_mul_exp_neg_sq_atTop.neg
  · simpa [hPhi] using tendsto_mul_exp_neg_sq_atBot
  · simpa [hPhi] using tendsto_mul_exp_neg_sq_atTop
  · intro h
    have h0 := congrFun h 0
    simp [hoPsi] at h0

/-- The virial theorem applied to the harmonic-oscillator ground state. -/
