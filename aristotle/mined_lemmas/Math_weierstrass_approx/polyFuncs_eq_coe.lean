/-
# Weierstrass Approx
Category: Pure Mathematics
Target: Math.weierstrass_approx
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Polynomial

namespace Math

/-- The set of polynomial functions on `[a, b]`, viewed inside the space `C([a,b], ℝ)` of
continuous real-valued functions on `[a, b]` (a normed space under the sup norm). -/

theorem polyFuncs_eq_coe (a b : ℝ) :
    polyFuncs a b = (polynomialFunctions (Set.Icc a b) : Set C(Set.Icc a b, ℝ)) := by
  rw [polynomialFunctions_coe]
  ext g
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, by ext x; simpa using (hp x).symm⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p, by intro x; rfl⟩

/-- **Weierstrass approximation theorem**: the polynomial functions are dense in the space
`C([a, b], ℝ)` of continuous real-valued functions on a closed interval, equipped with the
sup norm. -/
