/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory

/-!
## Setting

We work in three-dimensional configuration space.  A many-body fermionic state is
described here by the two quantities that enter the Lieb–Thirring argument:

* its total kinetic energy `T = ⟨Ψ, (-Δ₁ - ⋯ - Δ_N) Ψ⟩`,
* its one-body density `ρ`, normalised by `∫ ρ = N`.

The deep analytic input of the theory — the Lieb–Thirring inequality at `γ = 1` in
dimension `3` — is recorded as the predicate `LiebThirringBound`.  It is stated in
its *variational* form, which is the form in which it is used, and which is
equivalent to the eigenvalue-sum formulation by the min–max principle: for every
external potential `V`, the energy of the state in `-Δ + V` is bounded below by
`- L ∫ V₋^{5/2}`.

Everything below this input is proved here:

* `legendre_pointwise` — the pointwise Legendre/Young inequality, obtained from
  Mathlib's `Real.young_inequality` for the Hölder-conjugate pair `(5/2, 5/3)`;
* `kinetic_energy_bound` — the duality passage to the Thomas–Fermi-type kinetic
  energy inequality `T ≥ K_L ∫ ρ^{5/3}`, with the explicit constant
  `K_L = (3/5)(2/(5L))^{2/3}`;
* `liebThirringBound_of_kinetic` — the converse, showing that the two forms are in
  fact equivalent (so the hypothesis is not vacuous);
* `integral_rpow_four_thirds_le` — the Hölder interpolation
  `∫ ρ^{4/3} ≤ (∫ρ)^{1/2} (∫ρ^{5/3})^{1/2}`, obtained from Mathlib's
  `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`;
* `lieb_thirring_stability` — stability of matter of the second kind,
  `E ≥ -C·(N + K)`.
-/

/-- Configuration space of a single particle: three-dimensional Euclidean space. -/
abbrev Space : Type := EuclideanSpace ℝ (Fin 3)

/-- The negative part `V₋ = max (-V) 0` of a potential (a nonnegative function). -/

noncomputable def ltKineticConst (L : ℝ) : ℝ := (3 / 5) * (2 / (5 * L)) ^ ((2 : ℝ) / 3)

