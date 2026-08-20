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

set_option grind.warning false

/-!
## Overview

This file formalises the *sharpness of the phase transition* for the ferromagnetic Ising
model, in the form established by Duminil-Copin (with Tassion): below the critical
inverse temperature the two-point function decays exponentially fast, while above it the
two-point function does not tend to zero.  There is no intermediate regime.

The development is organised as follows.

* `Frontier.IsingBox` : a finite volume ferromagnetic Ising model, with an explicit
  Gibbs weight, partition function, expectation and two-point function.  We prove the
  basic structural facts: the partition function is positive, expectations of bounded
  observables are bounded, the two-point function is bounded by `1` and is a
  differentiable function of the inverse temperature, the spontaneous magnetisation with
  free boundary conditions vanishes (global spin-flip symmetry) and the two-point
  function vanishes at `β = 0` (single-site spin-flip symmetry).

* `Frontier.gronwall_bound` : the analytic heart of the Duminil-Copin–Tassion argument.
  From the differential inequality
  `n * θ n s ≤ (∑ k < n, θ k s) * (θ n)' s`
  one deduces, by integrating the logarithmic derivative, the quantitative bound
  `θ n β ≤ exp ( - (β' - β) * n / ∑ k < n, θ k β')` for `β < β'`.

* `Frontier.exp_decay_of_bounded_sums` : if in addition the partial sums
  `∑ k < n, θ k β'` are bounded, the previous bound is genuine exponential decay.

* `Frontier.IsingSharpnessSetup` : the Ising two-point functions of a sequence of finite
  volumes, together with the two monotonicity/positivity inputs (Griffiths' inequalities)
  and the Duminil-Copin–Tassion differential inequality (the deep input coming from the
  random-current representation, which is taken as a hypothesis here).

* `Frontier.duminil_ising_sharp` : the sharpness dichotomy for the critical parameter
  `Frontier.IsingSharpnessSetup.betaC`.

Finally `Frontier.trivialSetup` exhibits a concrete `IsingSharpnessSetup`, so that the
hypotheses of the main theorem are consistent.
-/

namespace Frontier

/-! ## Spins and spin flips -/

/-- The real value `±1` of a Boolean spin variable. -/

theorem exp_decay_of_bounded_sums
    (θ : ℕ → ℝ → ℝ) (B : ℝ)
    (hnonneg : ∀ n, ∀ β ∈ Set.Icc (0:ℝ) B, 0 ≤ θ n β)
    (hle : ∀ n, ∀ β ∈ Set.Icc (0:ℝ) B, θ n β ≤ 1)
    (hmono : ∀ n, MonotoneOn (θ n) (Set.Icc 0 B))
    (hdiff : ∀ n, Differentiable ℝ (θ n))
    (hdct : ∀ (n : ℕ), 1 ≤ n → ∀ s ∈ Set.Ioo 0 B,
      (n : ℝ) * θ n s ≤ (∑ k ∈ Finset.range n, θ k s) * deriv (θ n) s)
    {β β' C : ℝ} (hβ : 0 ≤ β) (hlt : β < β') (hβ' : β' ≤ B)
    (hbdd : ∀ n, (∑ k ∈ Finset.range n, θ k β') ≤ C) (n : ℕ) :
    θ n β ≤ Real.exp (-((β' - β) / C) * n) := by
  have hmemβ : β ∈ Set.Icc (0:ℝ) B := ⟨hβ, le_trans hlt.le hβ'⟩
  have hmemβ' : β' ∈ Set.Icc (0:ℝ) B := ⟨le_trans hβ hlt.le, hβ'⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simpa using hle 0 β hmemβ
  set Sg : ℝ := ∑ k ∈ Finset.range n, θ k β' with hSg
  have hSg0 : 0 ≤ Sg := Finset.sum_nonneg fun k _ => hnonneg k β' hmemβ'
  have hncast : (0:ℝ) < n := Nat.cast_pos.mpr hn
  rcases eq_or_lt_of_le hSg0 with h0 | hpos
  · -- degenerate case: all the `θ k β'`, `k < n`, vanish; then `θ n` vanishes below `β'`
    have hmid : β < (β + β') / 2 := by linarith
    have hmid2 : (β + β') / 2 < β' := by linarith
    have hsmem : (β + β') / 2 ∈ Set.Ioo (0:ℝ) B :=
      ⟨lt_of_le_of_lt hβ hmid, lt_of_lt_of_le hmid2 hβ'⟩
    have hSs0 : (∑ k ∈ Finset.range n, θ k ((β + β') / 2)) = 0 := by
      refine le_antisymm ?_
        (Finset.sum_nonneg fun k _ => hnonneg k _ ⟨hsmem.1.le, hsmem.2.le⟩)
      calc (∑ k ∈ Finset.range n, θ k ((β + β') / 2))
          ≤ Sg := Finset.sum_le_sum fun k _ =>
            hmono k ⟨hsmem.1.le, hsmem.2.le⟩ ⟨le_trans hβ hlt.le, hβ'⟩ hmid2.le
        _ = 0 := h0.symm
    have hd := hdct n hn _ hsmem
    rw [hSs0, zero_mul] at hd
    have hθmid : θ n ((β + β') / 2) ≤ 0 := by nlinarith
    have hθβ : θ n β ≤ 0 :=
      le_trans (hmono n ⟨hβ, le_trans hlt.le hβ'⟩ ⟨hsmem.1.le, hsmem.2.le⟩ hmid.le) hθmid
    exact le_trans hθβ (Real.exp_pos _).le
  · have hbase := gronwall_bound θ B hnonneg hle hmono hdiff hdct hβ hlt hβ' n
    refine le_trans hbase (Real.exp_le_exp.mpr ?_)
    rw [← hSg]
    rw [neg_div, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div]
    have h1 : Sg ≤ C := hbdd n
    have h2 : 0 ≤ (β' - β) * (n:ℝ) := mul_nonneg (by linarith) hncast.le
    gcongr

/-! ## Sharpness for the Ising model -/

/-- The two-point function between the two marked sites of the `n`-th box, as a function
of the inverse temperature. -/
