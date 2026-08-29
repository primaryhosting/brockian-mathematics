/-
# Weierstrass Approx
Category: Pure Mathematics
Target: Math.weierstrass_approx
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

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

namespace Math

open Polynomial

/-- The set of continuous functions on `[a,b]` that are restrictions of polynomials. -/
def polyRestrictions (a b : ℝ) : Set C(Set.Icc a b, ℝ) :=
  {g | ∃ p : ℝ[X], p.toContinuousMapOn (Set.Icc a b) = g}

/-- `polyRestrictions a b` is exactly the carrier of the subalgebra of polynomial functions. -/
theorem polyRestrictions_eq_coe (a b : ℝ) :
    polyRestrictions a b = (polynomialFunctions (Set.Icc a b) : Set C(Set.Icc a b, ℝ)) := by
  rw [polynomialFunctions_coe]
  ext g
  simp [polyRestrictions, eq_comm]

/-- **The Weierstrass approximation theorem.**
Polynomials (restricted to `[a,b]`) are dense in `C([a,b], ℝ)` with the sup norm. -/
theorem weierstrass_approx (a b : ℝ) : Dense (polyRestrictions a b) := by
  have h := polynomialFunctions_closure_eq_top a b
  have h2 : closure (polynomialFunctions (Set.Icc a b) : Set C(Set.Icc a b, ℝ)) = Set.univ := by
    have : ((polynomialFunctions (Set.Icc a b)).topologicalClosure :
        Set C(Set.Icc a b, ℝ)) = ((⊤ : Subalgebra ℝ C(Set.Icc a b, ℝ)) : Set _) := by
      rw [h]
    simpa [Subalgebra.topologicalClosure] using this
  rw [dense_iff_closure_eq, polyRestrictions_eq_coe, h2]

/-- Epsilon form of the Weierstrass approximation theorem: every continuous function on `[a,b]`
is within `ε` of a polynomial in the sup norm. -/
theorem weierstrass_approx_eps (a b : ℝ) (f : C(Set.Icc a b, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ‖p.toContinuousMapOn (Set.Icc a b) - f‖ < ε := by
  obtain ⟨g, hg, hgf⟩ :=
    Metric.mem_closure_iff.mp ((weierstrass_approx a b).closure_eq ▸ Set.mem_univ f) ε hε
  obtain ⟨p, rfl⟩ := hg
  exact ⟨p, by rw [← dist_eq_norm, dist_comm]; exact hgf⟩

/-- Pointwise form: a function continuous on `[a,b]` is uniformly approximated on `[a,b]`
by polynomials. -/
theorem weierstrass_approx_pointwise (a b : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b))
    {ε : ℝ} (hε : 0 < ε) : ∃ p : ℝ[X], ∀ x ∈ Set.Icc a b, |p.eval x - f x| < ε :=
  exists_polynomial_near_of_continuousOn a b f hf ε hε

end Math

