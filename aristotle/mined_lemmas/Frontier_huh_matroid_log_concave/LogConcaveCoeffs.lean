import Mathlib

/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
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

set_option grind.warning false

namespace Frontier

open Finset Polynomial

variable {α : Type*}

/-- The natural-number rank function of a matroid. -/

def LogConcaveCoeffs (p : ℤ[X]) : Prop :=
  ∀ k : ℕ, |p.coeff k| * |p.coeff (k + 2)| ≤ |p.coeff (k + 1)| ^ 2

/-- Log-concavity of the binomial coefficients: `C(n,k) * C(n,k+2) ≤ C(n,k+1)^2`. -/
