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

lemma theta_diff_ineq (n : ℕ) (β : ℝ) (hβ : 0 ≤ β) :
    (n : ℝ) * theta n β * (1 - theta n β)
      ≤ (∑ k ∈ Finset.range n, theta k β) * deriv (theta n) β := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set p : ℝ := phi β with hp
  set s : ℝ := max (1 - β) 0 with hs
  have hs0 : 0 ≤ s := le_max_right _ _
  have hs1 : s ≤ 1 := max_le (by linarith) (by norm_num)
  have hp0 : 0 < p := phi_pos β
  have hp1 : p ≤ 1 := phi_le_one β
  have hS : (∑ k ∈ Finset.range n, theta k β) = ∑ k ∈ Finset.range n, p ^ k := rfl
  have hgeom : (∑ k ∈ Finset.range n, p ^ k) * (p - 1) = p ^ n - 1 := geom_sum_mul p n
  have hSnn : 0 ≤ ∑ k ∈ Finset.range n, p ^ k :=
    Finset.sum_nonneg fun k _ => pow_nonneg hp0.le k
  -- the key pointwise inequality `1 - p ≤ 2 s`
  have hkey : 1 - p ≤ 2 * s := by
    have h1 : 1 - p ≤ vfun β := one_sub_phi_le β
    have h2 : vfun β = s ^ 2 := by rw [vfun, hs]
    nlinarith [hs0, hs1]
  have hpow : p ^ n = p ^ (n - 1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hS, theta_deriv n β]
  have hleft : (n : ℝ) * theta n β * (1 - theta n β)
      = (n : ℝ) * p ^ n * ((1 - p) * (∑ k ∈ Finset.range n, p ^ k)) := by
    have : (1 - p ^ n) = (1 - p) * ∑ k ∈ Finset.range n, p ^ k := by
      have := hgeom
      nlinarith [hgeom]
    rw [theta, ← hp, this]
  rw [hleft]
  have hfac : (∑ k ∈ Finset.range n, p ^ k) * ((n : ℝ) * p ^ (n - 1) * (p * (2 * s)))
      = (n : ℝ) * p ^ n * ((2 * s) * (∑ k ∈ Finset.range n, p ^ k)) := by
    rw [hpow]; ring
  rw [hfac]
  have hnn : 0 ≤ (n : ℝ) * p ^ n := by positivity
  have := mul_le_mul_of_nonneg_right hkey hSnn
  exact mul_le_mul_of_nonneg_left this hnn

/-- The explicit family assembles into a valid `IsingSharpnessData`. -/
