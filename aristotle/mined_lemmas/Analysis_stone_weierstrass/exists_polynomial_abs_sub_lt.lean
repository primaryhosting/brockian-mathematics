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

theorem exists_polynomial_abs_sub_lt (a b : ℝ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Set.Icc a b, |p.eval x - f x| < ε := by
  let f' : C(Set.Icc a b, ℝ) := ⟨fun x => f x, continuousOn_iff_continuous_restrict.mp hf⟩
  obtain ⟨p, hp⟩ := exists_polynomial_norm_sub_lt a b f' hε
  refine ⟨p, fun x hx => ?_⟩
  rw [norm_lt_iff _ hε] at hp
  exact hp ⟨x, hx⟩

end Analysis

