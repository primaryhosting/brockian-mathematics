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

/-- **Stone–Weierstrass theorem (polynomial form).**

On a compact interval `[a, b] ⊆ ℝ`, the subalgebra of polynomial functions is dense in the
algebra `C([a,b], ℝ)` of continuous real-valued functions with the uniform norm: its
topological closure is the whole algebra.

This is Mathlib's `polynomialFunctions_closure_eq_top`. -/
theorem stone_weierstrass (a b : ℝ) :
    (polynomialFunctions (Set.Icc a b)).topologicalClosure = ⊤ :=
  polynomialFunctions_closure_eq_top a b

/-- Every continuous function on `[a, b]` lies in the closure of the polynomial functions. -/
theorem stone_weierstrass_mem_closure (a b : ℝ) (f : C(Set.Icc a b, ℝ)) :
    f ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure := by
  rw [stone_weierstrass a b]
  exact Algebra.mem_top

/-- Epsilon form: every continuous function on `[a, b]` is uniformly approximated to within any
`ε > 0` by a polynomial function. -/
theorem stone_weierstrass_eps (a b : ℝ) (f : C(Set.Icc a b, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, ∀ x : Set.Icc a b, |p.eval (x : ℝ) - f x| < ε := by
  have h : f ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure :=
    stone_weierstrass_mem_closure a b f
  rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe, mem_closure_iff_seq_limit] at h
  obtain ⟨g, hg_mem, hg_tendsto⟩ := h
  rw [Metric.tendsto_atTop] at hg_tendsto
  obtain ⟨n, hn⟩ := hg_tendsto ε hε
  have hn' : dist (g n) f < ε := hn n le_rfl
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℝ,
      Polynomial.toContinuousMapOn p (Set.Icc a b) = g n := by
    have := hg_mem n
    rw [polynomialFunctions_coe] at this
    obtain ⟨p, hp⟩ := this
    exact ⟨p, hp⟩
  refine ⟨p, fun x => ?_⟩
  have hle : |g n x - f x| ≤ dist (g n) f := by
    simpa [Real.dist_eq] using ContinuousMap.dist_apply_le_dist (f := g n) (g := f) x
  have key : Polynomial.eval (x : ℝ) p = g n x := by
    rw [← hp]
    simp [Polynomial.toContinuousMapOn_apply]
  rw [key]
  exact lt_of_le_of_lt hle hn'

end Analysis

