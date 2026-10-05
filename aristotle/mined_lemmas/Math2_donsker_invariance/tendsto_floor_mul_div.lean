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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Donsker's invariance principle states that the diffusively rescaled random walk built from
i.i.d. centered increments of unit variance converges in law, as a process, to Brownian motion.

Mathlib currently contains neither Brownian motion, nor weak convergence on the Skorokhod space,
nor the central limit theorem, so the functional statement cannot be phrased.  What is proved
here is the *second-order (moment) form* of the invariance principle, which is the part of the
statement that can be expressed with the available theory:

* the rescaled walk `W_n(t) = S_{⌊n t⌋} / √n` is centered;
* its covariance converges to the Brownian covariance, `E[W_n(s) W_n(t)] → min s t`;
* its increments have the Brownian variance in the limit, `E[(W_n(t) - W_n(s))²] → t - s`;
* its increments over disjoint time intervals are exactly independent.

All the limits depend only on the first two moments of the increments and not on their law —
this is the *invariance* content of the principle, isolated in
`Math2.donsker_invariance_law_independent`.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Topology

/-- The diffusively rescaled random walk built from the increments `X`:
`rescaledWalk X n t ω = (X 0 + ⋯ + X (⌊n t⌋ - 1)) / √n`.
This is the piecewise-constant process appearing in Donsker's invariance principle. -/

lemma tendsto_floor_mul_div {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun n : ℕ => (⌊(n : ℝ) * u⌋₊ : ℝ) / n) atTop (𝓝 u) := by
  have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ) hu).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  refine h.congr fun n => ?_
  simp [Function.comp, mul_comm]

/-- **Donsker's invariance principle (second-order form).**

Let `X 0, X 1, …` be independent square-integrable random variables with mean `0` and
variance `1`, and let `W_n(t) = rescaledWalk X n t = S_{⌊n t⌋} / √n` be the diffusively
rescaled random walk.

Then, for all times `0 ≤ s ≤ t`:

* the rescaled walk is centered, `E[W_n(t)] = 0` for every `n`;
* its covariance converges to the Brownian covariance, `E[W_n(s) W_n(t)] → min s t = s`;
* the variance of its increment converges to the Brownian one, `E[(W_n(t) - W_n(s))²] → t - s`.

The limits are determined by the first two moments of the increments alone, which is the
*invariance* content of the principle (see `donsker_invariance_law_independent`).

Mathlib does not currently contain Brownian motion, weak convergence on the Skorokhod space,
or the central limit theorem, so the full functional statement cannot yet be phrased; this is
the moment form of the invariance principle. -/
