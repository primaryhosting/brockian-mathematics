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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Phys

/-! ## Part I: an abstract twist (flux insertion) estimate

We model a quantum system on a finite configuration space `α`: states are functions
`ψ : α → ℂ`, the (squared) norm is `∑ c, ‖ψ c‖^2`, and a Hamiltonian is a matrix
`H : α → α → ℂ`.  `qf H ψ` is the energy expectation `⟪ψ, H ψ⟫` (real part).
-/

section Abstract

variable {α : Type*} [Fintype α]

/-- The energy expectation value `⟪ψ, H ψ⟫` (real part). -/

lemma cos_bound {y δ : ℝ} {k : ℤ} (h : |y - 2 * Real.pi * k| ≤ δ) :
    |2 * Real.cos y - 2| ≤ δ ^ 2 := by
  set x := y - 2 * Real.pi * k with hx
  have hcos : Real.cos y = Real.cos x := by
    rw [hx, show y - 2 * Real.pi * k = y - k * (2 * Real.pi) by ring, Real.cos_sub_int_mul_two_pi]
  rw [hcos]
  have h1 : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  have h2 : Real.cos x ≤ 1 := Real.cos_le_one x
  have h3 : x ^ 2 ≤ δ ^ 2 := by nlinarith [sq_abs x, abs_nonneg x, h]
  rw [abs_le]
  constructor <;> nlinarith

/-- Off-diagonal matrix elements are controlled by the row sums. -/
