/-
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

/-!
## Sharpness of the phase transition (Duminil-Copin–Tassion)

The analytic engine behind Duminil-Copin's proof of sharpness of the phase transition for the
Ising model (and Bernoulli percolation) is a differential inequality of the form

  `(f n)' (p) ≥ (n / ∑_{k < n} f k (p)) · f n (p) · (1 - f n (p))`,

where `f n (p)` is a finite-volume order parameter at scale `n` (e.g. the two-point function
`⟨σ₀ σ_{∂Λ_n}⟩_β`, or the probability of a connection to the boundary of the box of size `n`)
at parameter `p` (playing the role of the inverse temperature).

Below we formalise this setting abstractly (`Frontier.IsDCTFamily`), define the critical
parameter as the supremum of the parameters at which the order parameters are summable
(`Frontier.criticalPoint`), and prove the **sharpness dichotomy**: strictly below the critical
parameter the order parameters decay *exponentially* fast, while strictly above it they are not
even summable, so in particular no exponential decay can hold. There is no intermediate regime.
-/

/-- The hypotheses of the Duminil-Copin–Tassion differential inequality.
`f n` is a finite-volume order parameter at scale `n`, taking values in `[0,1]`, nondecreasing
in the parameter `p ∈ [0,1]`, differentiable with derivative `fd n`, and satisfying the
differential inequality `n · f n p · (1 - f n p) ≤ (∑_{k < n} f k p) · (f n)' p`. -/
structure IsDCTFamily (f fd : ℕ → ℝ → ℝ) : Prop where
  /-- The order parameters take values in `[0,1]`. -/
  mem_Icc : ∀ (n : ℕ), ∀ p ∈ Set.Icc (0 : ℝ) 1, f n p ∈ Set.Icc (0 : ℝ) 1
  /-- The order parameters are nondecreasing in the parameter. -/
  mono : ∀ (n : ℕ), MonotoneOn (f n) (Set.Icc (0 : ℝ) 1)
  /-- `fd n` is the derivative of `f n`. -/
  hasDeriv : ∀ (n : ℕ), ∀ p ∈ Set.Icc (0 : ℝ) 1,
    HasDerivWithinAt (f n) (fd n p) (Set.Icc (0 : ℝ) 1) p
  /-- The Duminil-Copin–Tassion differential inequality. -/
  ineq : ∀ (n : ℕ), 1 ≤ n → ∀ p ∈ Set.Icc (0 : ℝ) 1,
    (n : ℝ) * f n p * (1 - f n p) ≤ (∑ k ∈ Finset.range n, f k p) * fd n p

/-- The critical parameter of a family of order parameters: the supremum of the set of
parameters in `[0,1]` at which the order parameters are summable. -/

lemma exponential_decay_of_summable (h : IsDCTFamily f fd) {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p < q) (hq : q ≤ 1) (hsum : Summable (fun k : ℕ => f k q)) :
    ∃ c > 0, ∀ᶠ n in Filter.atTop, f n p ≤ Real.exp (-c * (n : ℝ)) := by
  have hqI : q ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hp (le_of_lt hpq), hq⟩
  have hnonneg : ∀ k : ℕ, 0 ≤ f k q := fun k => (h.mem_Icc k q hqI).1
  set S : ℝ := (∑' k : ℕ, f k q) + 1 with hSdef
  have htsum0 : 0 ≤ ∑' k : ℕ, f k q := tsum_nonneg hnonneg
  have hS : 0 < S := by rw [hSdef]; linarith
  refine ⟨(q - p) / S, div_pos (by linarith) hS, ?_⟩
  have h2 : ∀ᶠ n : ℕ in Filter.atTop, f n q ≤ 1 / 2 := by
    have htend := hsum.tendsto_atTop_zero
    filter_upwards [htend (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with n hn
    exact le_of_lt hn
  filter_upwards [h2, Filter.eventually_ge_atTop 1] with n hfn hn
  have hSb : ∀ s ∈ Set.Icc p q, (∑ k ∈ Finset.range n, f k s) ≤ S := by
    intro s hs
    have hsI : s ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hp hs.1, le_trans hs.2 hq⟩
    have hstep : (∑ k ∈ Finset.range n, f k s) ≤ ∑ k ∈ Finset.range n, f k q :=
      Finset.sum_le_sum fun k _ => h.mono k hsI hqI hs.2
    have hstep2 : (∑ k ∈ Finset.range n, f k q) ≤ ∑' k : ℕ, f k q :=
      hsum.sum_le_tsum _ (fun i _ => hnonneg i)
    rw [hSdef]; linarith
  have hkey := key_ineq h hn hp (le_of_lt hpq) hq hS hSb
  have hpI : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hp, le_trans (le_of_lt hpq) hq⟩
  have hfp := h.mem_Icc n p hpI
  have hfq := h.mem_Icc n q hqI
  have hexp : (0 : ℝ) < Real.exp (-((n : ℝ) * (q - p) / S)) := Real.exp_pos _
  have harg : -((q - p) / S) * (n : ℝ) = -((n : ℝ) * (q - p) / S) := by ring
  rw [harg]
  -- `f n p * (1 - f n q) ≤ f n q * (1 - f n p) * E` with `f n q ≤ 1/2` gives `f n p ≤ E`
  have hlow : f n p * (1 / 2 : ℝ) ≤ f n p * (1 - f n q) := by
    have := hfp.1
    nlinarith
  have hhigh : f n q * (1 - f n p) * Real.exp (-((n : ℝ) * (q - p) / S))
      ≤ (1 / 2 : ℝ) * Real.exp (-((n : ℝ) * (q - p) / S)) := by
    have h1 : (0 : ℝ) ≤ 1 - f n p := by linarith [hfp.2]
    have hb : f n q * (1 - f n p) ≤ 1 / 2 := by nlinarith [hfq.1, hfp.1]
    exact mul_le_mul_of_nonneg_right hb hexp.le
  linarith

end Key

/-- **Sharpness of the phase transition** (abstract Duminil-Copin–Tassion form).

For a family of finite-volume order parameters satisfying the Duminil-Copin–Tassion
differential inequality, with critical parameter `pc = criticalPoint f`:

* (subcritical phase) for every `p ∈ [0, pc)` the order parameters decay *exponentially* fast:
  there is `c > 0` with `f n p ≤ exp (-c n)` for all large `n`;
* (supercritical phase) for every `p ∈ (pc, 1]` the order parameters are not summable, and in
  particular no exponential decay can hold.

Thus the transition is sharp: there is no intermediate regime of subexponential decay. -/
