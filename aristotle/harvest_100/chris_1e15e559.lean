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
theorem polynomialFunctions_topologicalClosure_eq_top_of_ge {a b : ℝ} (h : b ≤ a) :
    (polynomialFunctions (Set.Icc a b)).topologicalClosure = ⊤ := by
  have : Subsingleton (Set.Icc a b) := (Set.subsingleton_Icc_of_ge h).coe_sort
  subsingleton

/-- **The Stone–Weierstrass theorem, polynomial form.**

On a compact interval `[a, b] ⊆ ℝ`, the polynomial functions form a subalgebra of
`C([a, b], ℝ)` whose closure, in the topology of uniform convergence, is the whole space
of continuous functions. -/
theorem stone_weierstrass (a b : ℝ) :
    (polynomialFunctions (Set.Icc a b)).topologicalClosure = ⊤ := by
  rcases lt_or_ge a b with h | h
  · exact polynomialFunctions_topologicalClosure_eq_top_of_lt h
  · exact polynomialFunctions_topologicalClosure_eq_top_of_ge h

/-- Every continuous function on `[a, b]` lies in the closure of the polynomial functions. -/
theorem mem_polynomialFunctions_topologicalClosure (a b : ℝ) (f : C(Set.Icc a b, ℝ)) :
    f ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure := by
  rw [stone_weierstrass a b]
  exact Algebra.mem_top

/-- Uniform-norm form of the Stone–Weierstrass theorem: every continuous function on `[a, b]`
is within `ε` of a polynomial, in the uniform norm. -/
theorem exists_polynomial_norm_sub_lt (a b : ℝ) (f : C(Set.Icc a b, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ‖p.toContinuousMapOn (Set.Icc a b) - f‖ < ε := by
  have w := mem_closure_iff_frequently.mp (mem_polynomialFunctions_topologicalClosure a b f)
  rw [Metric.nhds_basis_ball.frequently_iff] at w
  obtain ⟨-, H, ⟨m, ⟨-, rfl⟩⟩⟩ := w ε hε
  rw [Metric.mem_ball, dist_eq_norm] at H
  exact ⟨m, H⟩

/-- Pointwise `ε`-form: any function continuous on `[a, b]` is uniformly approximated there
by polynomials. -/
theorem exists_polynomial_abs_sub_lt (a b : ℝ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Set.Icc a b, |p.eval x - f x| < ε := by
  let f' : C(Set.Icc a b, ℝ) := ⟨fun x => f x, continuousOn_iff_continuous_restrict.mp hf⟩
  obtain ⟨p, hp⟩ := exists_polynomial_norm_sub_lt a b f' hε
  refine ⟨p, fun x hx => ?_⟩
  rw [norm_lt_iff _ hε] at hp
  exact hp ⟨x, hx⟩

end Analysis

