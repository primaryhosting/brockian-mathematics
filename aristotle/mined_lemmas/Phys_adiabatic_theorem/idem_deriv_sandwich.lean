/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

open Set

/-- **Uniqueness for a linear ODE in a Banach algebra.**
If `X : ℝ → F` solves the linear differential equation `X' t = A t * X t` with continuous
coefficient `A` and vanishing initial datum, then `X` vanishes identically. -/

theorem idem_deriv_sandwich {R : Type*} [Ring R] {p d : R} (hp : p * p = p)
    (hd : d * p + p * d = d) : p * d * p = 0 := by
  have h := congrArg (fun x => p * x) hd
  simp only [mul_add, ← mul_assoc, hp] at h
  simpa using h

/-- The defining algebraic property of **Kato's generator** `[d, p] = d * p - p * d`:
its commutator with `p` reproduces `-d`. -/
