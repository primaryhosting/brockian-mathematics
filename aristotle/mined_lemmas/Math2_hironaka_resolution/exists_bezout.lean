/-
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
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

namespace Math2

open MvPolynomial

variable {k : Type*} [Field k]

/-- The affine plane curve `C_{p,q} : y^p = x^q`, as a polynomial in two variables. -/

lemma exists_bezout {p q : ℕ} (h : Nat.Coprime p q) : ∃ a b : ℤ, a * p + b * q = 1 := by
  refine ⟨Nat.gcdA p q, Nat.gcdB p q, ?_⟩
  have := Nat.gcd_eq_gcd_ab p q
  rw [h] at this
  push_cast at this ⊢
  linarith [this]

section

variable {p q : ℕ}

