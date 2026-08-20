/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Donsker's invariance principle

This file proves Donsker's invariance principle at the level of finite dimensional
distributions, for a random walk with independent standard Gaussian steps.

If `(X i)` are independent standard Gaussian random variables, `S n = X 0 + ⋯ + X (n-1)` and
`W n t = S ⌊n t⌋ / √n` is the diffusively rescaled walk, then for every nondecreasing sequence
of nonnegative times `t 0 ≤ t 1 ≤ ⋯` and every bounded continuous `f : ℝ^k → ℝ`,
`E[f (W n (t 0), …, W n (t (k-1)))]` converges to `E[f (B (t 0), …, B (t (k-1)))]`, where `B` is
any Brownian motion; that is, the finite dimensional distributions of the rescaled walk converge
weakly to those of Brownian motion.

## Main results

* `Math2.donsker_invariance`: the statement above, with the limit expressed through an
  arbitrary process `B` satisfying `Math2.IsBrownianMotion`.
* `Math2.donsker_invariance_law`: the same convergence with the limit written explicitly as the
  finite dimensional Wiener law `Math2.wienerFdd k t`, a statement which involves no Brownian
  motion at all.
* `Math2.covStep_wienerFdd`: the limit law is the centered Gaussian law on `ℝ^k` with covariance
  `min (t i) (t j)`, i.e. the covariance of Brownian motion.
* `Math2.map_brownian_eq_wienerFdd`: any Brownian motion sampled at the times `t` has law
  `wienerFdd k t`.
* `Math2.exists_gaussian_steps`: the assumptions on the steps of the walk are satisfiable.

## Implementation notes

Weak convergence is expressed, as usual, by convergence of the integrals of bounded continuous
test functions.  The law of each finite dimensional vector is identified through its
characteristic function (`Math2.charFun_map_linear`), and the convergence then follows from
dominated convergence, since all the laws involved are images of a fixed standard Gaussian
measure under linear maps depending continuously on the (rescaled) times.

The steps of the walk are assumed to be standard Gaussian.  Brownian motion is axiomatised
through its finite dimensional distributions (`Math2.IsBrownianMotion`); no path regularity is
required, and no construction of Brownian motion is carried out here — this is why the
Brownian-motion-free version `Math2.donsker_invariance_law` is also proved.
-/

open MeasureTheory ProbabilityTheory Filter Topology WithLp
open scoped NNReal

namespace Math2

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `IsBrownianMotion B P` says that the real valued process `(B t)_{t ≥ 0}` is a Brownian
motion under the probability measure `P`: it starts at `0`, it has independent increments, and
the increment over `[s, r]` is centered Gaussian with variance `r - s`.

Only the finite dimensional distributions are described here (no path regularity is required);
this is exactly what is needed for the convergence of finite dimensional distributions in
Donsker's theorem. -/
structure IsBrownianMotion (B : ℝ → Ω → ℝ) (P : Measure Ω) : Prop where
  /-- Each `B s` is measurable. -/
  measurable : ∀ s, Measurable (B s)
  /-- The process starts at `0`. -/
  start_zero : ∀ᵐ ω ∂P, B 0 ω = 0
  /-- The increment over `[s, r]` is centered Gaussian with variance `r - s`. -/
  gaussian_increment : ∀ s r : ℝ, 0 ≤ s → s ≤ r →
    P.map (fun ω ↦ B r ω - B s ω) = gaussianReal 0 (Real.toNNReal (r - s))
  /-- The increments along any nondecreasing sequence of times are independent. -/
  indep_increments : ∀ (m : ℕ) (v : ℕ → ℝ), Monotone v → 0 ≤ v 0 →
    iIndepFun (fun (i : Fin m) ω ↦ B (v ((i : ℕ) + 1)) ω - B (v (i : ℕ)) ω) P

/-! ### Gaussian vectors with independent increments -/

/-- `stepMap σ z j = ∑_{i ≤ j} σ i * z i`: the partial sums of the rescaled coordinates. -/

def covStep {k : ℕ} (σ : Fin k → ℝ) (j j' : Fin k) : ℝ :=
  ∑ i, if i ≤ j ∧ i ≤ j' then σ i ^ 2 else 0

/-! ### Characteristic function computations -/

/-- The characteristic function of a finite sum of independent real random variables is the
product of the characteristic functions. -/
