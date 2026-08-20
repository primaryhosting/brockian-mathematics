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

theorem exp_decay_of_lt_betaC {β : ℝ} (hβ : 0 ≤ β) (hlt : β < D.betaC) :
    ∃ c > 0, ∃ C > 0, ∀ n : ℕ, D.theta n β ≤ C * Real.exp (-c * n) := by
  obtain ⟨β₁, hβ₁mem, hββ₁⟩ :=
    exists_lt_of_lt_csSup D.subcritical_nonempty hlt
  obtain ⟨hβ₁0, hsum⟩ := hβ₁mem
  set L : ℝ := max 1 (∑' n, D.theta n β₁) with hLdef
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hS : ∀ (n : ℕ), ∀ x ∈ Set.Icc β β₁, (∑ k ∈ Finset.range n, D.theta k x) ≤ L := by
    intro n x hx
    have h1 : (∑ k ∈ Finset.range n, D.theta k x)
        ≤ ∑ k ∈ Finset.range n, D.theta k β₁ :=
      Finset.sum_le_sum fun k _ => D.mono_beta k hx.2
    have h2 : (∑ k ∈ Finset.range n, D.theta k β₁) ≤ ∑' k, D.theta k β₁ :=
      Summable.sum_le_tsum _ (fun k _ => D.nonneg k β₁) hsum
    exact (h1.trans h2).trans (le_max_right _ _)
  -- eventually `θ_n(β₁) ≤ 1/2`
  have htend : Filter.Tendsto (fun n => D.theta n β₁) Filter.atTop (nhds 0) :=
    hsum.tendsto_atTop_zero
  have hev : ∀ᶠ n in Filter.atTop, D.theta n β₁ ≤ 1 / 2 := by
    exact htend.eventually_le_const (by norm_num : (0:ℝ) < 1/2)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨(β₁ - β) / (2 * L), div_pos (by linarith) (by linarith), Real.exp ((β₁ - β) / (2 * L) * N),
    Real.exp_pos _, ?_⟩
  intro n
  set c : ℝ := (β₁ - β) / (2 * L) with hc
  have hcpos : 0 < c := by rw [hc]; exact div_pos (by linarith) (by linarith)
  by_cases hn : N ≤ n
  · have hstep := D.exp_decay_step hβ hββ₁.le hL (hS n) (hN n hn)
    have h1 : D.theta n β ≤ Real.exp (-(c * n)) := by
      refine hstep.trans ?_
      have : (n : ℝ) * (β₁ - β) / (2 * L) = c * n := by rw [hc]; ring
      rw [this]
      calc D.theta n β₁ * Real.exp (-(c * n)) ≤ 1 * Real.exp (-(c * n)) :=
            mul_le_mul_of_nonneg_right (D.le_one n β₁) (Real.exp_pos _).le
        _ = Real.exp (-(c * n)) := one_mul _
    refine h1.trans ?_
    have h2 : (1 : ℝ) ≤ Real.exp (c * N) :=
      Real.one_le_exp (mul_nonneg hcpos.le (Nat.cast_nonneg N))
    calc Real.exp (-(c * n)) = 1 * Real.exp (-c * n) := by ring_nf
      _ ≤ Real.exp (c * N) * Real.exp (-c * n) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  · push_neg at hn
    have h1 : D.theta n β ≤ 1 := D.le_one n β
    refine h1.trans ?_
    have : Real.exp (c * N) * Real.exp (-c * n) = Real.exp (c * (N - n)) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    exact Real.one_le_exp (by nlinarith [hcpos, (Nat.cast_lt (α := ℝ)).2 hn])

end IsingSharpnessData

open IsingSharpnessData in
/-- **Sharpness of the phase transition for the Ising model** (Duminil-Copin, abstract form).

Given the Duminil-Copin–Tassion differential inequality for the finite-volume order
parameters `θ_n` of the Ising model, the critical inverse temperature `β_c` is sharp:

* `β_c ≥ 0`;
* for every `0 ≤ β < β_c` the correlations decay exponentially fast
  (there is no intermediate regime of slow decay);
* for every `β > β_c` the correlations are not summable (long-range order).
-/
