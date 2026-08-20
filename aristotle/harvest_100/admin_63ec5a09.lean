import Mathlib

/-!
# Weierstrass Approx
Category: Pure Mathematics
Target: Math.weierstrass_approx
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Polynomial

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

/-- **Weierstrass approximation theorem**: the polynomial functions are dense in
`C([a,b], ℝ)` for the sup norm.

The first conjunct says that the set of continuous functions on `[a,b]` arising as
restrictions of real polynomials is dense in `C([a,b], ℝ)` (whose norm is the sup norm).
The second conjunct is the concrete `ε`-form: for every continuous `f : C(Icc a b, ℝ)` and
every `ε > 0` there is a real polynomial `p` with `‖p|[a,b] - f‖ < ε`, equivalently
`|p.eval x - f x| < ε` for all `x ∈ [a,b]`. -/
theorem weierstrass_approx (a b : ℝ) :
    Dense {g : C(Set.Icc a b, ℝ) | ∃ p : ℝ[X], p.toContinuousMapOn (Set.Icc a b) = g} ∧
      ∀ (f : C(Set.Icc a b, ℝ)) (ε : ℝ), 0 < ε →
        ∃ p : ℝ[X], ‖p.toContinuousMapOn (Set.Icc a b) - f‖ < ε ∧
          ∀ x : Set.Icc a b, |p.eval (x : ℝ) - f x| < ε := by
  have key : ∀ (f : C(Set.Icc a b, ℝ)) (ε : ℝ), 0 < ε →
      ∃ p : ℝ[X], ‖p.toContinuousMapOn (Set.Icc a b) - f‖ < ε ∧
        ∀ x : Set.Icc a b, |p.eval (x : ℝ) - f x| < ε := by
    intro f ε hε
    obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap a b f ε hε
    refine ⟨p, hp, fun x => ?_⟩
    simpa [Real.norm_eq_abs] using (ContinuousMap.norm_lt_iff _ hε).mp hp x
  refine ⟨?_, key⟩
  intro f
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨p, hp, -⟩ := key f ε hε
  exact ⟨p.toContinuousMapOn (Set.Icc a b), ⟨p, rfl⟩, by rwa [dist_eq_norm, norm_sub_rev]⟩

end Math

#print axioms Math.weierstrass_approx

