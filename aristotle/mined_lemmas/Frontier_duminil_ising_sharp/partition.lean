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

noncomputable def partition (β : ℝ) : ℝ := ∑ σ : M.site → Bool, M.weight β σ

/-- The Gibbs expectation of an observable. -/
