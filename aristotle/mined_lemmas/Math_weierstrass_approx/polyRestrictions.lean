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
