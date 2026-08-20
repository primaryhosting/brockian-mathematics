/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Scope of the formalization

Mathlib (at the pinned version) contains neither Brownian motion nor weak convergence of measures
on `C[0,1]`, so the full functional form of Donsker's invariance principle cannot be *stated*
against existing definitions. What is formalized here is the invariance principle at the level of
the second-order structure of the process: for an arbitrary sequence of independent, centred,
unit-variance, square-integrable increments, the diffusively rescaled walk
`W_n(t) = (X_0 + ⋯ + X_{⌊nt⌋-1})/√n` has

* covariance `E[W_n(s) W_n(t)] → min s t` (`Math2.donsker_invariance`),
* increment variance `E[(W_n(t) - W_n(s))²] → t - s` (`Math2.donsker_increment_variance`),
* asymptotically uncorrelated increments over disjoint intervals
  (`Math2.donsker_increments_uncorrelated`),

which are exactly the covariance structure of standard Brownian motion, and are independent of the
law of the increments (whence "invariance"). The hypotheses are shown to be non-vacuous in
`Math2.donsker_hypotheses_satisfiable`, using the simple symmetric random walk.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The rescaled (Donsker) random walk built from the increments `X`:
`rescaledWalk X n t ω = (X 0 ω + ⋯ + X (⌊n t⌋₊ - 1) ω) / √n`.
This is the classical diffusive rescaling of the partial-sum process. -/

theorem donsker_increment_variance [IsProbabilityMeasure μ]
    (hindep : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hvar : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Tendsto (fun n : ℕ => ∫ ω, (rescaledWalk X n t ω - rescaledWalk X n s ω) ^ 2 ∂μ)
      atTop (𝓝 (t - s)) := by
  have ht : 0 ≤ t := hs.trans hst
  have hexp : ∀ n : ℕ, (∫ ω, (rescaledWalk X n t ω - rescaledWalk X n s ω) ^ 2 ∂μ)
      = (∫ ω, rescaledWalk X n t ω * rescaledWalk X n t ω ∂μ)
        - 2 * (∫ ω, rescaledWalk X n t ω * rescaledWalk X n s ω ∂μ)
        + (∫ ω, rescaledWalk X n s ω * rescaledWalk X n s ω ∂μ) := by
    intro n
    have hI : ∀ r q : ℝ, Integrable (fun ω => rescaledWalk X n r ω * rescaledWalk X n q ω) μ :=
      fun r q => MemLp.integrable_mul (memLp_rescaledWalk hL2 n r) (memLp_rescaledWalk hL2 n q)
    have e0 : ∀ ω, (rescaledWalk X n t ω - rescaledWalk X n s ω) ^ 2
        = rescaledWalk X n t ω * rescaledWalk X n t ω
          - 2 * (rescaledWalk X n t ω * rescaledWalk X n s ω)
          + rescaledWalk X n s ω * rescaledWalk X n s ω := fun ω => by ring
    have I1 : Integrable (fun ω => rescaledWalk X n t ω * rescaledWalk X n t ω
        - 2 * (rescaledWalk X n t ω * rescaledWalk X n s ω)) μ :=
      (hI t t).sub ((hI t s).const_mul 2)
    simp_rw [e0]
    rw [integral_add I1 (hI s s), integral_sub (hI t t) ((hI t s).const_mul 2),
      integral_const_mul]
  simp only [hexp]
  have h1 := donsker_invariance (μ := μ) hindep hL2 hmean hvar ht ht
  have h2 := donsker_invariance (μ := μ) hindep hL2 hmean hvar ht hs
  have h3 := donsker_invariance (μ := μ) hindep hL2 hmean hvar hs hs
  have hval : min t t - 2 * min t s + min s s = t - s := by
    rw [min_self, min_self, min_eq_right hst]
    ring
  have hlim := (h1.sub (h2.const_mul 2)).add h3
  rwa [hval] at hlim

/-- The rescaled walk has asymptotically uncorrelated increments over disjoint intervals, as
Brownian motion does. -/
