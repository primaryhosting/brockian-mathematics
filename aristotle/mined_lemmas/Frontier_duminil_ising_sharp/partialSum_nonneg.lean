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

lemma partialSum_nonneg (h : IsDCTFamily f fd) (n : ℕ) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ ∑ k ∈ Finset.range n, f k p :=
  Finset.sum_nonneg fun k _ => (h.mem_Icc k p hp).1

/-- **Key integrated differential inequality.**  If the partial sums `∑_{k<n} f k s` are bounded
by `S > 0` on `[p,q]`, then the "odds ratio" of `f n` at `p` is smaller than the one at `q` by a
factor `exp (-n (q-p)/S)`. -/
