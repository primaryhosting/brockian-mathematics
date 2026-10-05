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

open scoped Polynomial

/-- **Stone–Weierstrass theorem (polynomial form).**

On a compact interval `[a, b] ⊆ ℝ`, the subalgebra of polynomial functions is dense in the
algebra `C([a,b], ℝ)` of continuous real-valued functions with the uniform norm: its
topological closure is the whole space. -/

theorem stone_weierstrass_exists_polynomial (a b : ℝ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Set.Icc a b, |p.eval x - f x| < ε := by
  set g : C(Set.Icc a b, ℝ) := ⟨fun x => f x, continuousOn_iff_continuous_restrict.mp hf⟩ with hg
  have hmem : g ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure := by
    rw [stone_weierstrass a b]; trivial
  have hfreq := Metric.nhds_basis_ball.frequently_iff.mp (mem_closure_iff_frequently.mp hmem)
  obtain ⟨-, H, ⟨p, -, rfl⟩⟩ := hfreq ε hε
  rw [Metric.mem_ball, dist_eq_norm] at H
  refine ⟨p, fun x hx => ?_⟩
  have := (ContinuousMap.norm_lt_iff _ hε).mp H ⟨x, hx⟩
  simpa [hg] using this

end Analysis

