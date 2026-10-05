import Mathlib

/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
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

namespace Frontier

/-- Exponential decay from a strict contraction over a fixed scale `L`:
if `0 ≤ a n ≤ 1` and `a (n + L) ≤ c * a n` with `0 < c < 1`, then `a` decays exponentially. -/

theorem gronwall_lower {m : ℝ → ℝ} {b c0 : ℝ}
    (hcont : ContinuousOn m (Set.Ici b))
    (hdiff : ∀ x : ℝ, b < x → DifferentiableAt ℝ m x)
    (hder : ∀ x : ℝ, b < x → c0 * (1 - m x) ≤ deriv m x)
    (hm0 : 0 ≤ m b) :
    ∀ β : ℝ, b < β → 1 - Real.exp (-(c0 * (β - b))) ≤ m β := by
  intro β hβ
  set h : ℝ → ℝ := fun x => (1 - m x) * Real.exp (c0 * (x - b)) with hh
  have hderiv : ∀ x ∈ Set.Ioo b β, HasDerivAt h
      (-(deriv m x) * Real.exp (c0 * (x - b)) + (1 - m x) * (Real.exp (c0 * (x - b)) * c0)) x := by
    intro x hx
    have hm : HasDerivAt m (deriv m x) x := (hdiff x hx.1).hasDerivAt
    have h1 : HasDerivAt (fun y : ℝ => 1 - m y) (-(deriv m x)) x := by
      simpa using (hasDerivAt_const x (1:ℝ)).sub hm
    have hlin : HasDerivAt (fun y : ℝ => c0 * (y - b)) c0 x := by
      simpa using ((hasDerivAt_id x).sub_const b).const_mul c0
    exact h1.mul hlin.exp
  have hcontIcc : ContinuousOn h (Set.Icc b β) := by
    apply ContinuousOn.mul
    · exact continuousOn_const.sub (hcont.mono Set.Icc_subset_Ici_self)
    · fun_prop
  have hanti : AntitoneOn h (Set.Icc b β) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc b β) hcontIcc
    · rw [interior_Icc]
      intro x hx
      exact (hderiv x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hderiv x hx).deriv]
      have hexp : 0 < Real.exp (c0 * (x - b)) := Real.exp_pos _
      nlinarith [hder x hx.1]
  have hle : h β ≤ h b := hanti (Set.left_mem_Icc.2 hβ.le) (Set.right_mem_Icc.2 hβ.le) hβ.le
  simp only [hh] at hle
  simp at hle
  have hexp : 0 < Real.exp (c0 * (β - b)) := Real.exp_pos _
  have h5 : (1 - m β) ≤ (1 - m b) * Real.exp (-(c0 * (β - b))) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hexp]
    exact hle
  nlinarith [Real.exp_pos (-(c0 * (β - b))), hm0, h5]

/-- Abstract data describing an Ising-type model on a transitive graph:
`corr β n` is the two-point function `⟨σ₀ σₓ⟩_β` at distance `n`, `mag β` the
spontaneous magnetisation `⟨σ₀⟩⁺_β`, and `betaC` the threshold produced by the
Duminil-Copin–Tassion argument.  The fields record the two key inputs of that
argument: a strict contraction of the two-point function below `betaC`, and a
differential inequality for the magnetisation above `betaC`. -/
structure IsingSharpData where
  /-- the two-point function `⟨σ₀ σₓ⟩_β` for `x` at distance `n` from the origin -/
  corr : ℝ → ℕ → ℝ
  /-- the spontaneous magnetisation `⟨σ₀⟩⁺_β` -/
  mag : ℝ → ℝ
  /-- the critical parameter -/
  betaC : ℝ
  /-- constant in the differential inequality -/
  c0 : ℝ
  c0_pos : 0 < c0
  corr_nonneg : ∀ (β : ℝ) (n : ℕ), 0 ≤ corr β n
  corr_le_one : ∀ (β : ℝ) (n : ℕ), corr β n ≤ 1
  mag_nonneg : ∀ β : ℝ, 0 ≤ mag β
  mag_cont : ContinuousOn mag (Set.Ici betaC)
  /-- squared magnetisation is dominated by the two-point function -/
  mag_sq_le_corr : ∀ (β : ℝ) (n : ℕ), (mag β) ^ 2 ≤ corr β n
  /-- subcritical input: strict contraction of the two-point function at some scale -/
  subcritical : ∀ β : ℝ, 0 ≤ β → β < betaC →
    ∃ L : ℕ, 0 < L ∧ ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ n : ℕ, corr β (n + L) ≤ c * corr β n
  /-- supercritical input: the Duminil-Copin–Tassion differential inequality -/
  supercritical : ∀ β : ℝ, betaC < β →
    DifferentiableAt ℝ mag β ∧ c0 * (1 - mag β) ≤ deriv mag β

/-- **Sharpness of the phase transition for the Ising model** (Duminil-Copin), stated
as a Lean-checked reduction to the two inputs of the Duminil-Copin–Tassion argument.

Below the critical parameter the two-point function decays exponentially and the
spontaneous magnetisation vanishes; above it the magnetisation grows at least
linearly in `β - βc`. -/
