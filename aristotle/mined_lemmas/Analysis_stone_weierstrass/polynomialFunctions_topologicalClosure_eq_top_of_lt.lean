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

theorem polynomialFunctions_topologicalClosure_eq_top_of_lt {a b : ℝ} (h : a < b) :
    (polynomialFunctions (Set.Icc a b)).topologicalClosure = ⊤ := by
  -- Precomposition with the affine homeomorphism, as an algebra map.
  let W : C(Set.Icc a b, ℝ) →ₐ[ℝ] C(I, ℝ) := compRightAlgHom ℝ ℝ (iccHomeoI a b h).symm
  -- The same operation, as a homeomorphism of the spaces of continuous functions.
  let W' : C(Set.Icc a b, ℝ) ≃ₜ C(I, ℝ) := (iccHomeoI a b h).arrowCongr (.refl _)
  have w : (W : C(Set.Icc a b, ℝ) → C(I, ℝ)) = W' := rfl
  have p := polynomialFunctions_closure_eq_top'
  -- Pull back the equality of subalgebras along `W`.
  apply_fun fun s => s.comap W at p
  simp only [Algebra.comap_top] at p
  rw [Subalgebra.topologicalClosure_comap_homeomorph _ W W' w] at p
  rw [polynomialFunctions.comap_compRightAlgHom_iccHomeoI] at p
  exact p

/-- The degenerate case `b ≤ a`: then `[a, b]` has at most one point, so `C([a,b], ℝ)` is
a subsingleton and every subalgebra is everything. -/
