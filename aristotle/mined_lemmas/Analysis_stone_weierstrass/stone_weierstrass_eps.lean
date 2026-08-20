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

open Polynomial

/-- **Stone–Weierstrass theorem (polynomial form).**
On a compact interval `[a, b]`, the subalgebra of polynomial functions is dense in the
algebra `C([a,b], ℝ)` of real-valued continuous functions with the uniform topology:
its topological closure is the whole space. -/

theorem stone_weierstrass_eps (a b : ℝ) (f : C(Set.Icc a b, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x : ℝ, ∀ hx : x ∈ Set.Icc a b, |p.eval x - f ⟨x, hx⟩| < ε := by
  -- The closure of the polynomial functions is everything, so `f` is a limit of polynomials.
  have hmem : f ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure :=
    mem_closure_polynomialFunctions a b f
  have hmem' : f ∈ closure ((polynomialFunctions (Set.Icc a b)) : Set C(Set.Icc a b, ℝ)) := hmem
  -- Extract an element of the subalgebra within distance `ε/2` in the sup norm.
  obtain ⟨g, hg, hdist⟩ :=
    Metric.mem_closure_iff.mp hmem' (ε / 2) (by positivity)
  rw [polynomialFunctions_coe] at hg
  obtain ⟨p, hp⟩ := hg
  refine ⟨p, fun x hx => ?_⟩
  have hval : p.eval x = g ⟨x, hx⟩ := by
    rw [← hp]
    simp [Polynomial.toContinuousMapOnAlgHom_apply, Polynomial.toContinuousMapOn_apply,
      Polynomial.toContinuousMap_apply]
  have hle : |g ⟨x, hx⟩ - f ⟨x, hx⟩| ≤ ε / 2 := by
    have := ContinuousMap.dist_apply_le_dist (f := g) (g := f) ⟨x, hx⟩
    rw [Real.dist_eq] at this
    exact this.trans (le_of_lt (by rwa [dist_comm] at hdist))
  rw [hval]
  exact lt_of_le_of_lt hle (by linarith)

end Analysis

