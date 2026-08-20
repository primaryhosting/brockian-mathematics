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

noncomputable def data : IsingSharpnessData where
  theta := theta
  differentiable := fun n β => (theta_hasDerivAt n β).differentiableAt
  nonneg := fun n β => pow_nonneg (phi_pos β).le n
  le_one := fun n β => pow_le_one₀ (phi_pos β).le (phi_le_one β)
  mono_beta := fun n a b hab => pow_le_pow_left₀ (phi_pos a).le (phi_monotone hab) n
  diff_ineq := theta_diff_ineq
  summable_zero := by
    have h : ∀ n : ℕ, theta n 0 = (phi 0) ^ n := fun n => rfl
    simpa [h] using summable_geometric_of_lt_one (phi_pos 0).le
      (by
        have : vfun 0 = 1 := by norm_num [vfun]
        rw [phi, this]
        simp)
  exists_not_summable := by
    refine ⟨1, by norm_num, ?_⟩
    have h1 : ∀ n : ℕ, theta n 1 = 1 := by
      intro n
      have : vfun 1 = 0 := by norm_num [vfun]
      simp [theta, phi, this]
    intro hsum
    have := hsum.tendsto_atTop_zero
    rw [show (fun n : ℕ => theta n 1) = fun _ : ℕ => (1:ℝ) from funext h1] at this
    have h0 : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds this
    norm_num at h0

/-- The assumptions of `Frontier.IsingSharpnessData` are satisfiable. -/
