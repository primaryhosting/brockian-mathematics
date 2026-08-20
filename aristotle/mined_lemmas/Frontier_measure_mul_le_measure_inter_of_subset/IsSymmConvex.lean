import Mathlib
/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
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

open MeasureTheory ProbabilityTheory

namespace Frontier

/-- A set is *symmetric convex* if it is convex and invariant under `x ↦ -x`. -/

theorem IsSymmConvex.prod {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] {K : Set E} {L : Set F}
    (hK : IsSymmConvex K) (hL : IsSymmConvex L) : IsSymmConvex (K ×ˢ L) :=
  ⟨hK.1.prod hL.1, fun _ hx => ⟨hK.2 _ hx.1, hL.2 _ hx.2⟩⟩

/-- **Tensorization for box-shaped sets.** If `μ` and `ν` satisfy the correlation inequality,
then the product measure satisfies it for products of symmetric convex sets. -/
