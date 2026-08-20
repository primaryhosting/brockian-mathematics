/-
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
open scoped Classical

set_option maxHeartbeats 1000000

namespace Frontier

/--
Abstract data describing the finite-volume connectivity/correlation functions of the
Ising model together with the Duminil-Copin–Tassion differential inequality.

Here `theta n β` should be thought of as the finite-volume order parameter
`θ_n(β) = ⟨σ_0 ; σ_{∂Λ_n}⟩_β` (equivalently, in the random-current / FK representation, the
probability that the origin is connected to the boundary of the box of radius `n`) at inverse
temperature `β`.

The fields record the standard structural properties of this family:

* `theta` takes values in `[0,1]` and is nondecreasing in the inverse temperature `β`
  (Griffiths / FKG monotonicity);
* the key input, `diff_ineq`, is the Duminil-Copin–Tassion differential inequality obtained
  from the OSSS inequality (Duminil-Copin–Raoufi–Tassion),
  `θ_n'(β) ≥ (n / ∑_{k<n} θ_k(β)) · θ_n(β)(1 - θ_n(β))`,
  written here in the equivalent product form which avoids division;
* `summable_zero` records that at infinite temperature (`β = 0`) correlations are summable;
* `exists_not_summable` records that at sufficiently low temperature they are not
  (existence of a low-temperature ordered regime).
-/
structure IsingSharpnessData where
  /-- Finite-volume order parameter `θ_n(β)`. -/
  theta : ℕ → ℝ → ℝ
  /-- Each `θ_n` is a differentiable function of the inverse temperature. -/
  differentiable : ∀ n, Differentiable ℝ (theta n)
  /-- `θ_n(β) ≥ 0`. -/
  nonneg : ∀ n β, 0 ≤ theta n β
  /-- `θ_n(β) ≤ 1`. -/
  le_one : ∀ n β, theta n β ≤ 1
  /-- `θ_n` is nondecreasing in `β`. -/
  mono_beta : ∀ n, Monotone (theta n)
  /-- The Duminil-Copin–Tassion differential inequality. -/
  diff_ineq : ∀ (n : ℕ) (β : ℝ), 0 ≤ β →
      (n : ℝ) * theta n β * (1 - theta n β)
        ≤ (∑ k ∈ Finset.range n, theta k β) * deriv (theta n) β
  /-- At `β = 0` the correlations are summable. -/
  summable_zero : Summable (fun n => theta n 0)
  /-- There is an inverse temperature at which the correlations fail to be summable. -/
  exists_not_summable : ∃ β₀ : ℝ, 0 ≤ β₀ ∧ ¬ Summable (fun n => theta n β₀)

namespace IsingSharpnessData

variable (D : IsingSharpnessData)

/-- The set of inverse temperatures at which the correlations are summable
(the "subcritical" regime). -/

lemma vfun_hasDerivAt (β : ℝ) : HasDerivAt vfun (-2 * max (1 - β) 0) β := by
  rcases lt_trichotomy β 1 with h | h | h
  · have heq : vfun =ᶠ[nhds β] fun x : ℝ => (1 - x) ^ 2 := by
      filter_upwards [Iio_mem_nhds h] with x hx
      simp only [Set.mem_Iio] at hx
      simp [vfun, max_eq_left (by linarith : (0:ℝ) ≤ 1 - x)]
    have hd : HasDerivAt (fun x : ℝ => (1 - x) ^ 2) (-2 * (1 - β)) β := by
      have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1 : ℝ) β := by
        simpa using (hasDerivAt_id β).const_sub 1
      simpa [mul_comm, mul_assoc, mul_left_comm] using h1.pow 2
    rw [max_eq_left (by linarith : (0:ℝ) ≤ 1 - β)]
    exact hd.congr_of_eventuallyEq heq
  · subst h
    rw [show max (1 - (1:ℝ)) 0 = 0 by norm_num, mul_zero]
    rw [hasDerivAt_iff_tendsto_slope]
    have hsq : ∀ x : ℝ, ‖slope vfun 1 x‖ ≤ ‖x - 1‖ := by
      intro x
      rcases eq_or_ne x 1 with rfl | hx
      · simp [slope]
      · have hv1 : vfun 1 = 0 := by simp [vfun]
        have hs : slope vfun 1 x = vfun x / (x - 1) := by
          rw [slope_def_field]; simp [hv1]
        have habs : (0:ℝ) < |x - 1| := abs_pos.2 (sub_ne_zero.2 hx)
        rw [hs, Real.norm_eq_abs, abs_div, abs_of_nonneg (vfun_nonneg x),
          div_le_iff₀ habs, Real.norm_eq_abs]
        calc vfun x ≤ (x - 1) ^ 2 := vfun_le_sq x
          _ = |x - 1| * |x - 1| := by rw [abs_mul_abs_self]; ring
    have hg : Tendsto (fun x : ℝ => ‖x - 1‖) (nhdsWithin 1 {1}ᶜ) (nhds 0) := by
      have hc : Continuous (fun x : ℝ => ‖x - 1‖) := (continuous_id.sub continuous_const).norm
      have hct : Tendsto (fun x : ℝ => ‖x - 1‖) (nhds 1) (nhds 0) := by
        simpa using hc.tendsto (1:ℝ)
      exact hct.mono_left nhdsWithin_le_nhds
    exact squeeze_zero_norm (fun x => hsq x) hg
  · have heq : vfun =ᶠ[nhds β] fun _ : ℝ => (0:ℝ) := by
      filter_upwards [Ioi_mem_nhds h] with x hx
      simp only [Set.mem_Ioi] at hx
      simp [vfun, max_eq_right (by linarith : (1:ℝ) - x ≤ 0)]
    rw [max_eq_right (by linarith : (1:ℝ) - β ≤ 0), mul_zero]
    exact (hasDerivAt_const β (0:ℝ)).congr_of_eventuallyEq heq

