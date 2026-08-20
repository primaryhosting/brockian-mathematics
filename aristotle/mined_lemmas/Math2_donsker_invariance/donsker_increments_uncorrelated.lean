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

theorem donsker_increments_uncorrelated [IsProbabilityMeasure μ]
    (hindep : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hvar : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1)
    {s t u v : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) :
    Tendsto (fun n : ℕ => ∫ ω, (rescaledWalk X n t ω - rescaledWalk X n s ω) *
        (rescaledWalk X n v ω - rescaledWalk X n u ω) ∂μ) atTop (𝓝 0) := by
  have ht : 0 ≤ t := hs.trans hst
  have hu : 0 ≤ u := ht.trans htu
  have hv : 0 ≤ v := hu.trans huv
  have hexp : ∀ n : ℕ, (∫ ω, (rescaledWalk X n t ω - rescaledWalk X n s ω) *
      (rescaledWalk X n v ω - rescaledWalk X n u ω) ∂μ)
      = (∫ ω, rescaledWalk X n t ω * rescaledWalk X n v ω ∂μ)
        - (∫ ω, rescaledWalk X n t ω * rescaledWalk X n u ω ∂μ)
        - ((∫ ω, rescaledWalk X n s ω * rescaledWalk X n v ω ∂μ)
        - (∫ ω, rescaledWalk X n s ω * rescaledWalk X n u ω ∂μ)) := by
    intro n
    have hI : ∀ r q : ℝ, Integrable (fun ω => rescaledWalk X n r ω * rescaledWalk X n q ω) μ :=
      fun r q => MemLp.integrable_mul (memLp_rescaledWalk hL2 n r) (memLp_rescaledWalk hL2 n q)
    have e0 : ∀ ω, (rescaledWalk X n t ω - rescaledWalk X n s ω) *
        (rescaledWalk X n v ω - rescaledWalk X n u ω)
        = (rescaledWalk X n t ω * rescaledWalk X n v ω
            - rescaledWalk X n t ω * rescaledWalk X n u ω)
          - (rescaledWalk X n s ω * rescaledWalk X n v ω
            - rescaledWalk X n s ω * rescaledWalk X n u ω) := fun ω => by ring
    have I1 : Integrable (fun ω => rescaledWalk X n t ω * rescaledWalk X n v ω
        - rescaledWalk X n t ω * rescaledWalk X n u ω) μ := (hI t v).sub (hI t u)
    have I2 : Integrable (fun ω => rescaledWalk X n s ω * rescaledWalk X n v ω
        - rescaledWalk X n s ω * rescaledWalk X n u ω) μ := (hI s v).sub (hI s u)
    simp_rw [e0]
    rw [integral_sub I1 I2, integral_sub (hI t v) (hI t u), integral_sub (hI s v) (hI s u)]
  simp only [hexp]
  have h1 := donsker_invariance (μ := μ) hindep hL2 hmean hvar ht hv
  have h2 := donsker_invariance (μ := μ) hindep hL2 hmean hvar ht hu
  have h3 := donsker_invariance (μ := μ) hindep hL2 hmean hvar hs hv
  have h4 := donsker_invariance (μ := μ) hindep hL2 hmean hvar hs hu
  have : min t v - min t u - (min s v - min s u) = (0 : ℝ) := by
    rw [min_eq_left (htu.trans huv), min_eq_left htu,
      min_eq_left (hst.trans (htu.trans huv)), min_eq_left (hst.trans htu)]
    ring
  simpa [this] using ((h1.sub h2).sub (h3.sub h4))

/-! ### Non-vacuity: the hypotheses are satisfied by a simple random walk -/

/-- The fair coin measure on `Bool`. -/
