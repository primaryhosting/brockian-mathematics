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

def polyFuncs (a b : ℝ) : Set C(Set.Icc a b, ℝ) :=
  {g | ∃ p : ℝ[X], ∀ x : Set.Icc a b, g x = p.eval (x : ℝ)}

