import Mathlib
/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The Willmore conjecture (proved by Marques and Neves) states that every immersed torus
`Σ ⊆ ℝ³` satisfies `∫_Σ H² dA ≥ 2π²`, with equality (up to conformal transformations of
`ℝ³`) exactly for the Clifford torus, i.e. the torus of revolution whose radii satisfy
`R = √2 · r`.

This file formalizes and proves the *base case* of the conjecture: the case of tori of
revolution, which is Willmore's original computation and the case that fixes the constant
`2π²`.  Everything is done from first principles:

* for an arbitrary parametrized surface `X : ℝ → ℝ → ℝ³`, the tangent vectors
  `Frontier.surfDu`, `Frontier.surfDv` and the second derivatives are literally `deriv`s
  of `X`; `Frontier.surfMeanCurvature` is the mean curvature computed from the first and
  second fundamental forms, `Frontier.surfAreaElement` is the area element
  `‖X_u × X_v‖`, and `Frontier.willmoreEnergyOf` is the iterated integral `∫∫ H² dA`
  over a fundamental domain `[0, 2π] × [0, 2π]`;
* `Frontier.torusParam` is the usual parametrization of the torus of revolution with
  radii `R > r > 0`, and `Frontier.willmoreEnergy R r` its Willmore energy;
* `Frontier.IsImmersedTorus` and `Frontier.WillmoreConjectureStatement` record the
  statement of the conjecture in full generality.

The main results are

* `Frontier.torusMeanCurvature_eq` and `Frontier.torusAreaElement_eq`: the classical
  formulas `H = (R + 2r cos u) / (2r(R + r cos u))` and `dA = r (R + r cos u)`;
* `Frontier.integral_inv_add_cos` : `∫₀^{2π} du / (R + r cos u) = 2π / √(R² - r²)`;
* `Frontier.willmoreEnergy_eq` : `W(R, r) = π² R² / (r √(R² - r²))`;
* `Frontier.willmore_conjecture` : `2π²` is the least Willmore energy of a torus of
  revolution, and it is attained exactly by the Clifford torus `R = √2 · r`;
* `Frontier.willmore_bound_sharp` : the constant `2π²` in the general conjecture is
  attained by an immersed torus, so it cannot be improved.
-/

open Real Matrix

namespace Frontier

/-! ### Differential geometry of a parametrized surface in `ℝ³`

For a map `X : ℝ → ℝ → ℝ³` we define the tangent vectors, the first and second fundamental
forms, the area element and the mean curvature by the classical formulas.  All derivatives
are honest `deriv`s of `X`. -/

/-- The tangent vector `X_u`. -/

noncomputable def surfDu (X : ℝ → ℝ → Fin 3 → ℝ) (u v : ℝ) : Fin 3 → ℝ :=
  deriv (fun t => X t v) u

/-- The tangent vector `X_v`. -/
