import Mathlib

/-!
# Stone Weierstrass
Category: Frontier Wave 2 (deeper machinery)
Target: Analysis.stone_weierstrass
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Analysis

open ContinuousMap
open scoped unitInterval Polynomial

/-- The nondegenerate case `a < b`: the subalgebra of polynomial functions on `[a, b]` is
dense in `C([a, b], ℝ)`.  This is obtained from the Weierstrass approximation theorem on the
unit interval by pulling back along the affine homeomorphism `[a,b] ≃ₜ [0,1]`. -/

theorem exists_polynomial_norm_sub_lt (a b : ℝ) (f : C(Set.Icc a b, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ‖p.toContinuousMapOn (Set.Icc a b) - f‖ < ε := by
  have w := mem_closure_iff_frequently.mp (mem_polynomialFunctions_topologicalClosure a b f)
  rw [Metric.nhds_basis_ball.frequently_iff] at w
  obtain ⟨-, H, ⟨m, ⟨-, rfl⟩⟩⟩ := w ε hε
  rw [Metric.mem_ball, dist_eq_norm] at H
  exact ⟨m, H⟩

/-- Pointwise `ε`-form: any function continuous on `[a, b]` is uniformly approximated there
by polynomials. -/
